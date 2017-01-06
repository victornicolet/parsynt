open SketchTypes
open Utils
open SPretty

let debug = ref false

let auxiliary_variables : Cil.varinfo Utils.IH.t = IH.create 10
(**

*)
let is_a_hole h =
  match h with
  | SkHoleL _ | SkHoleR _ -> true
  | _ -> false

let type_of_hole h =
  match h with
  | SkHoleR t | SkHoleL (_, t) -> Some t
  | _ -> None


let rec make_holes ?(max_depth = 1) ?(is_final = false) (state : VS.t) =
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
           then SkHoleL (sklv, t), 1
           else SkHoleR t, 1)
      | SkArray (sklv, expr) ->
        (** Array : for now, cannot be a stv *)
        let t = type_of_var sklv in
        (match t with
        | Vector (t, _) -> SkHoleR t, 1
        | _ -> failwith "Unexpected type in array")
      | SkTuple vs -> SkVar (SkTuple vs), 0
    end

  | SkConst c ->
     begin
       match c with
       | CInt _ | CInt64 _ -> SkHoleR Integer, 1
       | CReal _ -> SkHoleR Real, 1
       | CBool _ -> SkHoleR Boolean, 1
       | _ -> SkHoleR Unit, 1
     end

  | SkFun skl -> SkFun (make_join ~state:state ~skip:[] skl), 0

  | SkBinop (op, e1, e2) ->
     let holes1, d1 = merge_leaves max_depth (make_holes state e1) in
     let holes2, d2 = merge_leaves max_depth (make_holes state e2) in
     SkBinop (op, holes1, holes2), max d1 d2

  | SkUnop (op, e) ->
     merge_leaves max_depth (make_holes state e)

  | SkCond (c, li, le) ->
     let ch, _ = make_holes state c in
     SkCond (ch ,
             make_join ~state:state ~skip:[] li,
             make_join ~state:state ~skip:[] le), 0

  | SkQuestion (c, ei, ee) ->
     let h1, d1  = merge_leaves max_depth (make_holes state ei) in
     let h2, d2 = merge_leaves max_depth (make_holes state ee) in
     let hc, dc = merge_leaves max_depth (make_holes state c) in
     SkQuestion (hc, h1, h2), max (max d1 d2) dc

  | SkApp (t, vo, args) ->
     let new_args, depths =
       ListTools.unpair (List.map (make_holes state) args) in
     SkApp (t, vo, new_args), ListTools.intlist_max depths

  | _ as skexpr ->  skexpr, 0

and make_join ~(state : VS.t) ~(skip: skLVar list) =
  function
  | SkLetExpr li ->
    SkLetExpr (List.map (fun (v, e) ->
        match e with
        | SkVar v when List.mem v skip -> (v, e)
        | _ -> (v, fst (make_holes ~is_final:true state e))) li)

  | SkLetIn (li, cont) ->
    let to_skip = fst (ListTools.unpair li) in
    SkLetIn (
      List.map (fun (v, e) ->
          match e with
          | SkVar v when List.mem v skip -> (v, e)
          | _ -> (v, fst (make_holes ~is_final:true state e))) li,
      make_join ~state:state ~skip:(skip@to_skip) cont)

and merge_leaves max_depth (e,d) =
  if d + 1 >= max_depth then
    begin
      match e with
      | SkUnop (op , h) when is_a_hole h ->
        let th = check_option (type_of_hole h) in
        let t_o = type_of_unop th op in
        (match t_o with
         | Some t ->
           if th = t then SkHoleR t, d else SkHoleR (Function (th, t)), d

         | None -> failwith "Type error in holes")

      | SkBinop (op, h1, h2) when is_a_hole h1 && is_a_hole h2 ->
        let t1 = check_option (type_of_hole h1) in
        let t2 = check_option (type_of_hole h2) in
        (match (type_of_binop (res_type t1) (res_type t2) op) with
         | Some t ->
           if t1 = t2 then
             SkHoleR (Function (t1, t)) , d
           else
             SkBinop(op, h1, h2), d + 1
         | None -> failwith "Type error in holes")

      | SkApp (t, ov, el) ->
        if List.fold_left (fun is_h e -> is_h && is_a_hole e) true el then
          SkHoleR t, d
        else
          let el', _ = ListTools.unpair
              (List.map (fun e_ -> merge_leaves max_depth (e_, d)) el)
          in SkApp (t, ov, el'), d

      | SkQuestion (c, ei, ee) ->
        begin
          if is_a_hole ei && is_a_hole ee && is_a_hole c then
            SkQuestion (SkHoleR Boolean, ei, ee), d
          else
            e, 0
        end
      (** Do not propagate expression depth into control statements*)
      | _ -> (e, 0)
    end
  else
    (e, d + 1)

let build (state : VS.t) (sklet : sklet) =
  make_join ~state:state ~skip:[] sklet
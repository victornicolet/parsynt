open Core.Std
open Utils
open SketchTypes
open SPretty
open Cil2Func
open Utils.ListTools
open VariableAnalysis

module VS = VS
module SM = Map.Make (String)
module Ct = CilTools

(**
   The main entry point of the file is build :
   build a sketch from the Floop (vector of functions
   for each state variable representing the ody of the
   loop).
*)

let debug = ref false

let skexpr_of_constant t c =
  let const =  match c with
    | Cil.CInt64 (i, ik, stro) ->
      if Ct.is_like_bool ik || (t = Boolean)
      then CBool (bool_of_int64 i)
      else CInt64 i
    | Cil.CReal (f, fk, stro) ->
      CReal f
    | Cil.CChr cr ->
      CChar cr
    | Cil.CStr s ->
      CString s
    | _ -> CBox c
  in SkConst const

let convert_const = skexpr_of_constant

(** Optimisations *)
let remove_simple_state_rewritings (var , expr) =
  match var, expr with
  | _ -> (var, expr)

let apply_remove sklet =
  match sklet with
  | SkLetExpr el -> sklet
  | SkLetIn (el, cont) ->
    let new_rewrites = List.map el ~f:remove_simple_state_rewritings in
    SkLetIn (new_rewrites, cont)

(**
   Rebuild && expressions that have been trasnformed by CIL into
    nested ifs.
*)

let rebuild_and_expressions (var, expr) =
  let to_rearrange expr =
    match expr with
    | SkQuestion (c, e1, e2) -> true
    | _ -> false
  in
  let rearrange_aux rfunc expr =
    match expr with
    | SkQuestion (c, e1, e2) ->
      let c = rfunc c in
      let e1' = rfunc e1 in
      let e2' = rfunc e2 in
      begin
        match e1', e2' with
        (* if (a) then b else false -> a && b *)
        | e1bis,  SkConst (CBool false)->
          SkBinop  (And, c, e1bis)
        (* if (a) then if (b) x : y else y -> if (a && b) then x else y *)
        | SkQuestion (c', e1bis, e1ter), e1ter' when e1ter = e1ter' ->
          SkQuestion (SkBinop (And, c, c'), e1bis, e1ter)
        | _ , _ -> expr
      end
    | _ -> failwith "Unexpected case."
  in
  (var, transform_expr to_rearrange rearrange_aux ident ident expr)

(**
   Rebuild or expressions that have been replaced by nested ifs with
   "true" branches.
*)
let rebuild_simple_or (var, expr) =
  let to_rearrange expr =
    match expr with
    | SkQuestion (c, e1, e2) -> true
    | _ -> false
  in
  let rearrange_aux rfunc expr =
    match expr with
    | SkQuestion (c, e1, e2) ->
      let c = rfunc c in
      let e1' = rfunc e1 in
      let e2' = rfunc e2 in
      begin
        match e1', e2' with
        (* if (a) then true else e --> a or e *)
        | SkConst (CBool true), e when type_of e = Boolean->
          SkBinop (Or, c, e)
        | _ , _ -> expr
      end
    | _ -> failwith "Unexpected case."
  in
  (var, transform_expr to_rearrange rearrange_aux ident ident expr)

(** Apply or- and and- rebuilding in expression tree *)
let rec apply_rearrange sklet =
  match sklet with
  | SkLetExpr el ->
    SkLetExpr (List.map ~f:rebuild_simple_or
                 (List.map ~f:rebuild_and_expressions el))
  | SkLetIn (el, cont) ->
    SkLetIn (List.map ~f:rebuild_simple_or
               (List.map ~f:rebuild_and_expressions el),
             apply_rearrange cont)


(** Enforce conversion of 0s and 1s that should be boolean *)
let force_boolean_constants (v, e) =
  let cast_bool_cst cst =
    match cst with
    | SkConst c ->
      let new_c =
        match c with
        | CInt 1 | CBool true | CInt64 1L -> CBool true
        | CInt 0 | CBool false | CInt64 0L -> CBool false
        | _ -> c
      in SkConst new_c
    | _ -> cst
  in
  let candidate flag e =
    match e with
    | SkBinop (op, _, _) when (op = Or || op  = And) -> true
    | SkQuestion (_, e1, e2) when (type_of e1 = Boolean) ||
                                  (type_of e2 = Boolean) -> true
    | _ -> flag
  in
  let force_bool flag rfunc e =
    match e with
    | SkBinop (op, e1, e2) when (op = Or || op  = And) ->
      let e1' = rfunc true e1 in let e2' = rfunc true e2 in
      SkBinop (op, cast_bool_cst e1', cast_bool_cst e2')

    | SkQuestion (c, e1, e2) when (type_of e1 = Boolean) ||
                                  (type_of e2 = Boolean) ||
                                  flag ->
      let e1' = rfunc true e1 in
      let e2' = rfunc true e2 in
      let c' = rfunc true c in
      SkQuestion (cast_bool_cst c', cast_bool_cst e1', cast_bool_cst e2')

    | _ -> rfunc false e
  in
  let v_is_bool = type_of_var v = Boolean in
  (v, transform_expr_flag v_is_bool candidate force_bool identity2 identity2 e)


(**
   Transform  simple boolean expressions with unnnecessary conditionals
   (if c true false) in c
*)
let transform_boolean_if_expression =
  let case e =
    match e with
    | SkQuestion (SkConst (CBool true), _, _) -> true
    | SkQuestion (SkConst (CBool false), _, _) -> true
    | SkQuestion (c, SkConst (CBool true), SkConst (CBool false)) -> true
    | SkBinop (Or, SkConst (CBool true), _)
    | SkBinop (Or,_, SkConst (CBool true)) -> true
    | SkBinop (Or, SkConst (CBool false), _)
    | SkBinop (Or,_, SkConst (CBool false)) -> true
    | SkBinop (And, SkConst (CBool true), _)
    | SkBinop (And,_, SkConst (CBool true)) -> true
    | SkBinop (And, SkConst (CBool false), _)
    | SkBinop (And,_, SkConst (CBool false)) -> true
    | _ -> false
  in
  let transform_bool rfunc e =
    match e with
    (* true ? a : b -> a *)
    | SkQuestion (SkConst (CBool true), e1, _) -> rfunc e1
    (* false ? a : b -> b *)
    | SkQuestion (SkConst (CBool false), _, e2) -> rfunc e2
    (* c ? true : false --> c *)
    | SkQuestion (c, SkConst (CBool true),SkConst (CBool false)) ->
      rfunc c
    (* true || c --> true *)
    | SkBinop (Or, SkConst (CBool true), _)
    (* c || true --> true *)
    | SkBinop (Or,_, SkConst (CBool true)) -> SkConst (CBool true)
    (* false || c --> c  and commut. *)
    | SkBinop (Or, SkConst (CBool false), c)
    | SkBinop (Or, c, SkConst (CBool false)) -> rfunc c
    (* true && c --> c and commut. *)
    | SkBinop (And, SkConst (CBool true), c)
    | SkBinop (And, c, SkConst (CBool true)) ->  rfunc c
    (* false && c --> false and commut. *)
    | SkBinop (And, SkConst (CBool false), _)
    | SkBinop (And,_, SkConst (CBool false)) -> SkConst (CBool false)

    | _ -> failwith "transform_boolean_expression : bad case"
  in
  transform_expr case
    transform_bool
    identity
    identity

(** Apply the boolean conversions *)
let booleanize (v, e) =
  v, (match type_of_var v with
      | Boolean -> transform_boolean_if_expression e
      | _ -> e)

let rec remove_boolean_ifs sklet =
  match sklet with
  | SkLetExpr el ->
    SkLetExpr (List.map ~f:booleanize
                 (List.map ~f:force_boolean_constants el))
  | SkLetIn (el, cont) ->
    SkLetIn (List.map ~f:booleanize
               (List.map ~f:force_boolean_constants el),
             remove_boolean_ifs cont)


(** Apply all optimizations *)
let optims sklet =
  let sklet' = apply_remove sklet in
  apply_rearrange ( remove_boolean_ifs sklet')



(** A class to build the sketch, initialized with a set containing all
    variables, the state varaibles, the function in pre-functionalized form,
    and the loop-bounds information.
    Build the sketch by calling the buuild method, and retrieve it with
    the get_sketch method.
*)

class sketch_builder
    (all_vs : VS.t)
    (stv : VS.t)
    (func : letin)
    figu =
  object (self)
    val mutable all_vars = all_vs
    val mutable state_vars = stv
    val mutable func = func
    val mutable figu = figu
    val mutable sketch = None

    method build =
      let rec convert (cur_v : skLVar)  =
        function
        | Var vi -> mkVarExpr vi

        (** TODO : array -> region *)
        | Array (vi, el) ->
          let skexpr_list = List.map el ~f:(convert cur_v) in
          mkVarExpr ~offsets:skexpr_list vi

        | FunApp (ef, arg_l) ->
          let is_c_def, vi_o, ty = is_exp_function ef in
          let sty = symb_type_of_ciltyp ty in
          let fargs =  List.map arg_l ~f:(convert cur_v) in
          if is_c_def then
            SkApp (sty, vi_o, fargs)
          else
            let fname = (check_option vi_o).Cil.vname in
            (match fargs with
             | [e] ->
               let unop = (check_option (symb_unop_of_fname fname)) in
               SkUnop (unop, e)
             | e1::[e2] ->
               let binop = (check_option (symb_binop_of_fname fname)) in
               SkBinop (binop, e1, e2)
             | _ -> SkApp (sty, vi_o, fargs))


        | Container (e, subs) ->
          let converted_substitutions = IM.map (convert cur_v) subs in
          convert_cils ~subs:converted_substitutions e

        | FQuestion (ec, e1, e2) ->
          SkQuestion (convert cur_v ec,
                      (convert cur_v e1),
                      (convert cur_v e2))

        | FRec ((i, g, u), expr) ->
          SkRec ((i, g, u), SkLetExpr [(cur_v, convert cur_v expr)])

        | FBinop (op, e1, e2) ->
          SkBinop (op, convert cur_v e1, convert cur_v e2)

        | FUnop (op, e) -> SkUnop (op, convert cur_v e)

        | FConst c -> SkConst c

        | FSizeof t -> SkSizeof (symb_type_of_ciltyp t)
        | FSizeofE e -> SkSizeofE (convert cur_v e)
        | FSizeofStr s -> SkSizeofStr s
        | FAlignof t -> SkAlignof (symb_type_of_ciltyp t)
        | FAlignofE e -> SkAlignofE (convert cur_v e)
        | FCastE (t, e) -> SkCastE (symb_type_of_ciltyp t, convert cur_v e)
        | FAddrof lval -> SkAddrof (skexpr_of_lval lval)
        | _ -> failwith "not yet implemented"


      and convert_cils ?(subs = IM.empty) ?(expect_ty = Bottom) =
        function
        | Cil.Const c -> skexpr_of_constant expect_ty c

        | Cil.Lval v ->
          let skvar = skexpr_of_lval v in
          begin
            match skvar with
            | SkVar (SkVarinfo vi) when IM.mem vi.Cil.vid subs ->
              IM.find vi.Cil.vid subs
            | _ -> skvar
          end

        | Cil.SizeOf t->
          let typ = symb_type_of_ciltyp t in
          SkSizeof typ

        | Cil.SizeOfE e ->
          SkSizeofE (convert_cils ~subs:subs e)

        | Cil.SizeOfStr s ->
          SkSizeofStr s

        | Cil.AlignOf t ->
          SkAlignof (symb_type_of_ciltyp t)

        | Cil.AlignOfE e ->
          SkAlignofE (convert_cils ~subs:subs e)

        | Cil.AddrOf lv ->
          SkAddrof (skexpr_of_lval lv)

        | Cil.AddrOfLabel stm_ref ->
          SkAddrofLabel stm_ref

        | Cil.UnOp (op, e1, t) ->
          let op', ex_ty = symb_unop_of_cil op in
          SkUnop (op',convert_cils ~subs:subs ~expect_ty:ex_ty e1)

        | Cil.BinOp (op, e1, e2, t) ->
          let op', ex_ty = symb_binop_of_cil op in
          (* != --->  (! (= )) *)
          if op' = Neq then
            SkUnop(Not,
                   SkBinop (Eq,
                            convert_cils ~subs:subs ~expect_ty:ex_ty e1,
                            convert_cils ~subs:subs ~expect_ty:ex_ty e2))
          else
            SkBinop (op',
                     convert_cils ~subs:subs ~expect_ty:ex_ty e1,
                     convert_cils ~subs:subs ~expect_ty:ex_ty e2)

        | Cil.Question (c, e1, e2, t) ->
          let c' = convert_cils ~expect_ty:Boolean c in
          SkQuestion (c',  convert_cils ~subs:subs e1,
                      convert_cils ~subs:subs e2)

        | Cil.CastE (t, e) ->
          let ty = symb_type_of_ciltyp t in
          SkCastE (ty , convert_cils ~subs:subs ~expect_ty:ty e)

        | Cil.StartOf lv ->
          SkStartOf (skexpr_of_lval lv)


      and convert_offset =
        function
        | Cil.NoOffset -> []
        | Cil.Index (e, offset) ->
          ((convert_cils e)::(convert_offset offset))
        | Cil.Field _ -> []

      and convert_offsets offsets_list =
        List.fold_left offsets_list
          ~init:[]
          ~f:(fun acc x -> acc@[convert_cils x])


      and skexpr_of_lval ((host, offset) : Cil.lval) =
        match convert_offset offset with
        (**
            A null list only means there is no offset in the offset part
            of the Cil.lval, but the offset might still in the expression
            if it is a Cil memory access.
        *)
        | [] ->
          let vo, ofs_li = analyze_host host in
          begin
            match vo with
            | Some vi ->
              mkVarExpr ~offsets:(convert_offsets ofs_li) vi
            | None -> failwith "Is it an lval ?"
          end

        | new_off_list ->
          let vo, prev_offs_list =  analyze_host host in
          let off_list = (convert_offsets prev_offs_list)@new_off_list in
          let vi_to_expr =
            match vo with
            | None ->
              (** Anonymous function with type *)
              (fun t x -> SkApp (t, None, off_list))
            | Some vi ->
              (fun t x -> x vi)
          in
          let t =  Cil.typeOfLval (host,offset) in
          vi_to_expr
            (symb_type_of_ciltyp t)
            (mkVarExpr ~offsets:off_list)




      (** TODO : add the current loop index *)
      and convert_letin letin =
        match letin with
        | State subs  ->
          let state =
            IM.mapi
              (fun k e ->
                 let cur_v =
                   try
                     SkVarinfo (VSOps.find_by_id k state_vars)
                   with Not_found -> SkVarinfo (VSOps.find_by_id k all_vars)
                 in
                 (cur_v, convert cur_v e))
              subs
          in
          let complete_state =
            VS.fold
              (fun state_vi l ->
                 l@[
                   if IM.mem state_vi.Cil.vid state
                   then IM.find state_vi.Cil.vid state
                   else (SkVarinfo state_vi, mkVarExpr state_vi)])
              state_vars []
          in
          SkLetExpr complete_state

        | Let (v, e, cont, i, loc) ->
          let cur_v = SkVarinfo v in
          SkLetIn ([(cur_v, convert cur_v e)], convert_letin cont)

        | LetRec (igu, let_body, let_cont, loc) ->
          (** Tail position *)
          if is_empty_state let_cont then
            SkLetExpr [(SkTuple state_vars,
                        SkRec (igu, convert_letin let_body))]
          else
            SkLetIn ([(SkTuple state_vars,
                       SkRec (igu, convert_letin let_body))],
                     convert_letin let_cont)

        | LetCond (c, let_if, let_else, let_cont, loc) ->
          if is_empty_state let_cont then
            SkLetExpr [(SkTuple state_vars,
                        SkCond (convert (SkTuple stv) c,
                                convert_letin let_if,
                                convert_letin let_else))]
          else
            SkLetIn ( [(SkTuple state_vars,
                        SkCond (convert (SkTuple stv) c,
                                convert_letin let_if,
                                convert_letin let_else))],
                      convert_letin let_cont)

      in

      let index, (ilet, gexpr, ulet) = figu in

      let iletin = convert_letin ilet in
      let uletin = convert_letin ulet in
      (** TODO implement records to manage index *)
      let gskexpr = convert (SkVarinfo (VS.max_elt index)) gexpr in
      sketch <- Some (optims (convert_letin func),
                      (index, (iletin, gskexpr, uletin)));

    method get_sketch = sketch
  end




(** Transform the converted sketch to a loop body and a join sketch *)

let rec make_conditional_guards (initial_vs : VS.t) (letin_form : sklet) =
  match letin_form with
  | SkLetIn (bindings, body) ->
    let new_bindings, new_state_vars = mk_cg bindings initial_vs in
    let new_body, state_vars' =
      make_conditional_guards new_state_vars body in
    SkLetIn (new_bindings, new_body), state_vars'

  | SkLetExpr bindings ->
    let new_bindings, new_state_vars = mk_cg bindings initial_vs in
    SkLetExpr new_bindings, new_state_vars

and mk_cg bindings vs =
  (List.fold
     bindings
     ~init: []
     ~f:(fun acc binding -> acc @ [mk_cg_binding vs binding])), vs

and mk_cg_binding vs ((var, expr) : skLVar * skExpr) =
  (var, expr)

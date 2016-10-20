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

let rec convert  (cur_v : skLVar)  =
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
     convert_cils ~cur_v:cur_v ~subs:converted_substitutions e

  | FQuestion (ecil, e1, e2) ->
     SkQuestion (convert_cils ~expect_ty:Boolean ecil,
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
  | FAddrof lval -> SkAddrof (skexpr_of_lval cur_v lval)
  | _ -> failwith "not yet implemented"


and convert_cils ?(cur_v = SkState) ?(subs = IM.empty) ?(expect_ty = Bottom) =
  function
  | Cil.Const c -> skexpr_of_constant expect_ty c

  | Cil.Lval v ->
     let skvar = skexpr_of_lval cur_v v in
     begin
       match skvar with
       | SkVar (SkVarinfo vi) when IM.mem vi.Cil.vid subs ->
          IM.find vi.Cil.vid subs
       | _ ->skvar
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
     SkAddrof (skexpr_of_lval cur_v lv)

  | Cil.AddrOfLabel stm_ref ->
     SkAddrofLabel stm_ref

  | Cil.UnOp (op, e1, t) ->
     let op', ex_ty = symb_unop_of_cil op in
     SkUnop (op',convert_cils ~subs:subs ~expect_ty:ex_ty e1)

  | Cil.BinOp (op, e1, e2, t) ->
     let op', ex_ty = symb_binop_of_cil op in
     SkBinop (op',
              convert_cils ~subs:subs ~expect_ty:ex_ty e1,
              convert_cils ~subs:subs ~expect_ty:ex_ty e2)

  | Cil.Question (c, e1, e2, t) ->
     let c' = convert_cils ~expect_ty:Boolean c in
     SkQuestion (c',  convert_cils ~subs:subs e1, convert_cils ~subs:subs e2)

  | Cil.CastE (t, e) ->
     let ty = symb_type_of_ciltyp t in
     SkCastE (ty , convert_cils ~subs:subs ~expect_ty:ty e)

  | Cil.StartOf lv ->
     SkStartOf (skexpr_of_lval cur_v lv)


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


and skexpr_of_lval (cur_v : skLVar)
    ((host, offset) : Cil.lval) =
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


and skexpr_of_constant t c =
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

(** TODO : add the current loop index *)
and convert_letin (vs : VS.t) letin =
  match letin with
    | State subs  ->
      let state =
        List.map (IM.bindings subs)
          ~f:(fun (k,e) ->
              let cur_v =
                try
                  SkVarinfo (VSOps.find_by_id k vs)
                with Not_found ->
                  (Format.eprintf "@.Not found occured while transforming @.%a\
                                   DIdn't find varaible id %i in %a"
                     (Cil2Func.pp_letin ?wloc:(Some false)) (vs, letin)
                     k VSOps.pvs vs;
                   raise Not_found)
              in
              (cur_v, convert cur_v e))
      in
      let complete_state =
        state@(List.map
                  (VSOps.varlist
                     (VS.filter (fun v -> not (IM.mem v.Cil.vid subs)) vs))
                  ~f:(fun vi -> (SkVarinfo vi, mkVarExpr vi)))
       in
       SkLetExpr complete_state

    | Let (v, e, cont, i, loc) ->
       let cur_v = SkVarinfo v in
       SkLetIn ([(cur_v, convert cur_v e)], convert_letin vs cont)

    | LetRec (igu, let_body, let_cont, loc) ->
       (** Tail position *)
       if is_empty_state let_cont then
         SkLetExpr [(SkState, SkRec (igu, convert_letin vs let_body))]
       else
         SkLetIn ([(SkState, SkRec (igu, convert_letin vs let_body))],
                  convert_letin vs let_cont)

    | LetCond (c, let_if, let_else, let_cont, loc) ->
       if is_empty_state let_cont then
         SkLetExpr [(SkState,
                     SkCond (convert_cils c,
                             convert_letin vs let_if,
                             convert_letin vs let_else))]
       else
          SkLetIn ( [(SkState,
                     SkCond (convert_cils c,
                             convert_letin vs let_if,
                             convert_letin vs let_else))],
                  convert_letin vs let_cont)
    | LetState (let_state, let_cont) ->
       SkLetIn ([(SkState, SkFun (convert_letin vs let_state))],
                convert_letin vs let_cont)

(** Optimisations *)
let remove_simple_state_rewritings (var , expr) =
  match var, expr with
  | SkState, SkFun (SkLetExpr li) ->
     begin
       match List.filter li
         ~f:(fun e -> match e with _, SkVar _ -> false |_, _-> true)
       with
       | [(v, e)] -> v, e
       | _ -> (var, expr)
     end
  | _ -> (var, expr)

let optims sklet =
  match sklet with
  | SkLetExpr el -> sklet
  | SkLetIn (el, cont) ->
     let new_rewrites = List.map el ~f:remove_simple_state_rewritings in
     SkLetIn (new_rewrites, cont)


(*** MAIN ENTRY POINT ***)

let build state let_form (index, (ilet, gexpr, ulet)) =
  let ext_state = VS.union state index in
  let iletin = convert_letin ext_state ilet in
  let uletin = convert_letin ext_state ulet in
  (** TODO implement records to manage index *)
  let gskexpr = convert (SkVarinfo (VS.max_elt index)) gexpr in
  optims (convert_letin state let_form), (index, (iletin, gskexpr, uletin))


let convert_const = skexpr_of_constant

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

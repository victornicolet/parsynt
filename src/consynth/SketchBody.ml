open Utils
open FuncTypes
open FPretty
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
  in FnConst const

let convert_const = skexpr_of_constant

(** Optimisations *)
let remove_simple_state_rewritings (var , expr) =
  match var, expr with
  | _ -> (var, expr)

let apply_remove fnlet =
  match fnlet with
  | FnLetExpr el -> fnlet
  | FnLetIn (el, cont) ->
    let new_rewrites = List.map remove_simple_state_rewritings el in
    FnLetIn (new_rewrites, cont)
  | e -> e
(**
   Rebuild && expressions that have been trasnformed by CIL into
    nested ifs.
*)

let rebuild_boolean_expressions (var, expr) =
  let to_rearrange expr =
    match expr with
    | FnQuestion (c, e1, e2) -> true
    | _ -> false
  in
  let rearrange_aux rfunc expr =
    match expr with
    | FnQuestion (c, e1, e2) ->
      let c = rfunc c in
      let e1' = rfunc e1 in
      let e2' = rfunc e2 in
      begin
        match e1', e2' with
        (* if (a) then b else false -> a && b *)
        | e1bis,  FnConst (CBool false)->
          rfunc (FnBinop  (And, c, e1bis))

        (* if (a) then true else b -> a || b *)
        | FnConst (CBool true), e when type_of e = Boolean->
          rfunc (FnBinop (Or, c, e))

        (* if (a) then if (b) x : y else y -> if (a && b) then x else y *)
        | FnQuestion (c', e1bis, e1ter), e1ter' when e1ter = e1ter' ->
          rfunc (FnQuestion (FnBinop (And, c, c'), e1bis, e1ter))
        (** Distributivity / associativity *)
        (* if (a) then (b || c) else c -> (a && b) || c) *)
        | FnBinop (Or, a, b1), b2 when b1 = b2 ->
          FnBinop(Or, FnBinop(And, a, c), b1)

        | _ , _ -> FnQuestion(c, e1', e2')
      end
    | _ -> failwith "Unexpected case."
  in
  (var, transform_expr to_rearrange rearrange_aux identity identity expr)


(** Apply or- and and- rebuilding in expression tree *)
let rec apply_rearrange fnlet =
  match fnlet with
  | FnLetExpr el ->
    FnLetExpr (List.map rebuild_boolean_expressions el)
  | FnLetIn (el, cont) ->
    FnLetIn (List.map rebuild_boolean_expressions el,
             apply_rearrange cont)
  | e -> e

(** Enforce conversion of 0s and 1s that should be boolean *)
let force_boolean_constants (v, e) =
  let cast_bool_cst cst =
    match cst with
    | FnConst c ->
      let new_c =
        match c with
        | CInt 1 | CBool true | CInt64 1L -> CBool true
        | CInt 0 | CBool false | CInt64 0L -> CBool false
        | _ -> c
      in FnConst new_c
    | _ -> cst
  in
  let candidate flag e =
    match e with
    | FnBinop (op, _, _) when (op = Or || op  = And) -> true
    | FnQuestion (_, e1, e2) when (type_of e1 = Boolean) ||
                                  (type_of e2 = Boolean) -> true
    | _ -> flag
  in
  let force_bool flag rfunc e =
    match e with
    | FnBinop (op, e1, e2) when (op = Or || op  = And) ->
      let e1' = rfunc true e1 in let e2' = rfunc true e2 in
      FnBinop (op, cast_bool_cst e1', cast_bool_cst e2')

    | FnQuestion (c, e1, e2) when (type_of e1 = Boolean) ||
                                  (type_of e2 = Boolean) ||
                                  flag ->
      let e1' = rfunc true e1 in
      let e2' = rfunc true e2 in
      let c' = rfunc true c in
      FnQuestion (cast_bool_cst c', cast_bool_cst e1', cast_bool_cst e2')

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
    | FnQuestion (FnConst (CBool true), _, _) -> true
    | FnQuestion (FnConst (CBool false), _, _) -> true
    | FnQuestion (c, FnConst (CBool true), FnConst (CBool false)) -> true
    | FnBinop (Or, FnConst (CBool true), _)
    | FnBinop (Or,_, FnConst (CBool true)) -> true
    | FnBinop (Or, FnConst (CBool false), _)
    | FnBinop (Or,_, FnConst (CBool false)) -> true
    | FnBinop (And, FnConst (CBool true), _)
    | FnBinop (And,_, FnConst (CBool true)) -> true
    | FnBinop (And, FnConst (CBool false), _)
    | FnBinop (And,_, FnConst (CBool false)) -> true
    | _ -> false
  in
  let transform_bool rfunc e =
    match e with
    (* true ? a : b -> a *)
    | FnQuestion (FnConst (CBool true), e1, _) -> rfunc e1
    (* false ? a : b -> b *)
    | FnQuestion (FnConst (CBool false), _, e2) -> rfunc e2
    (* c ? true : false --> c *)
    | FnQuestion (c, FnConst (CBool true),FnConst (CBool false)) ->
      rfunc c
    (* true || c --> true *)
    | FnBinop (Or, FnConst (CBool true), _)
    (* c || true --> true *)
    | FnBinop (Or,_, FnConst (CBool true)) -> FnConst (CBool true)
    (* false || c --> c  and commut. *)
    | FnBinop (Or, FnConst (CBool false), c)
    | FnBinop (Or, c, FnConst (CBool false)) -> rfunc c
    (* true && c --> c and commut. *)
    | FnBinop (And, FnConst (CBool true), c)
    | FnBinop (And, c, FnConst (CBool true)) ->  rfunc c
    (* false && c --> false and commut. *)
    | FnBinop (And, FnConst (CBool false), _)
    | FnBinop (And,_, FnConst (CBool false)) -> FnConst (CBool false)

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

let rec remove_boolean_ifs fnlet =
  match fnlet with
  | FnLetExpr el ->
    FnLetExpr (List.map booleanize
                 (List.map force_boolean_constants el))
  | FnLetIn (el, cont) ->
    FnLetIn (List.map booleanize
               (List.map force_boolean_constants el),
             remove_boolean_ifs cont)
  | e -> e

let rec isolate_set_array (fnlet : fnExpr) =
  let rec split_bindings bindings pre =
    match bindings with
    | hd :: tl ->
      (match hd with
      | FnArray (a,i) , e -> (pre, Some hd, tl)
      | _ -> split_bindings tl (pre@[hd]))

    | [] -> (pre, None, [])
  in
  match fnlet with
  | FnLetIn (el, cont) ->
    let pre, mid, rest = split_bindings el [] in
    (match mid with
    | Some mid ->
      FnLetIn(pre, FnLetIn([mid], isolate_set_array (FnLetIn(rest, cont))))
    | None ->
      FnLetIn(el, isolate_set_array cont))
  | e -> e

(** Apply all optimizations *)
let optims fnlet =
  let fnlet' = apply_remove fnlet in
  isolate_set_array (apply_rearrange (remove_boolean_ifs fnlet'))


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
    (_figu : VS.t * (letin * expr * letin)) =
  object (self)
    val mutable all_vars = all_vs
    val mutable state_vars = stv
    val mutable func = func
    val mutable figu = _figu
    val mutable sketch = None
    val mutable global_bound =
      let _, (_, guard, _) = _figu in
      match guard with
      | FBinop (Lt, _, Var vn) -> Some vn
      | FBinop (Le, _, Var vn) -> Some vn
      | FBinop (Gt, Var vn, _) -> Some vn
      | FBinop (Ge, Var vn, _) -> Some vn
      | _ -> None
    val mutable uses_global_bound = false

    method is_global_bound vi =
      match global_bound with
      | Some vn -> vi = vn
      | None -> false

    method build =
      let rec convert =
        function
        | Var vi ->
          (if self#is_global_bound vi then uses_global_bound <- true
           else ());
          mkVarExpr (var_of_vi vi)

        (** TODO : array -> region *)
        | Array (vi, el) ->
          let expr_list = List.map convert el in
          mkVarExpr ~offsets:expr_list (var_of_vi vi)

        | FunApp (ef, arg_l) ->
          let is_c_def, vi_o, ty = is_exp_function ef in
          let sty = type_of_ciltyp ty in
          let fargs =  List.map convert arg_l in
          if is_c_def then
            FnApp (sty, (var_of_vi ==> vi_o), fargs)
          else
            let fname = (check_option vi_o).Cil.vname in
            (match fargs with
             | [e] ->
               let unop = (check_option (symb_unop_of_fname fname)) in
               FnUnop (unop, e)
             | e1::[e2] ->
               let binop = (check_option (symb_binop_of_fname fname)) in
               FnBinop (binop, e1, e2)
             | _ -> FnApp (sty, var_of_vi ==> vi_o, fargs))


        | Container (e, subs) ->
          let converted_substitutions = IM.map convert subs in
          convert_cils ~subs:converted_substitutions e

        | FQuestion (ec, e1, e2) ->
          FnQuestion (convert ec,
                      (convert e1),
                      (convert e2))


        | FBinop (op, e1, e2) ->
          FnBinop (op, convert e1, convert e2)

        | FUnop (op, e) -> FnUnop (op, convert e)

        | FConst c -> FnConst c

        | FSizeof t -> FnSizeof (type_of_ciltyp t)
        | FSizeofE e -> FnSizeofE (convert e)
        | FSizeofStr s -> FnSizeofStr s
        | FAlignof t -> FnAlignof (type_of_ciltyp t)
        | FAlignofE e -> FnAlignofE (convert e)
        | FCastE (t, e) -> FnCastE (type_of_ciltyp t, convert e)
        | FAddrof lval -> FnAddrof (skexpr_of_lval lval)
        | _ -> failwith "not yet implemented"


      and convert_cils ?(subs = IM.empty) ?(expect_ty = Bottom) =
        function
        | Cil.Const c -> skexpr_of_constant expect_ty c

        | Cil.Lval v ->
          let skvar = skexpr_of_lval v in
          begin
            match skvar with
            | FnVar (FnVariable vi) when IM.mem vi.vid subs ->
              IM.find vi.vid subs
            | _ -> skvar
          end

        | Cil.SizeOf t->
          let typ = type_of_ciltyp t in
          FnSizeof typ

        | Cil.SizeOfE e ->
          FnSizeofE (convert_cils ~subs:subs e)

        | Cil.SizeOfStr s ->
          FnSizeofStr s

        | Cil.AlignOf t ->
          FnAlignof (type_of_ciltyp t)

        | Cil.AlignOfE e ->
          FnAlignofE (convert_cils ~subs:subs e)

        | Cil.AddrOf lv ->
          FnAddrof (skexpr_of_lval lv)

        | Cil.AddrOfLabel stm_ref ->
          FnAddrofLabel stm_ref

        | Cil.UnOp (op, e1, t) ->
          let op', ex_ty = symb_unop_of_cil op in
          FnUnop (op',convert_cils ~subs:subs ~expect_ty:ex_ty e1)

        | Cil.BinOp (op, e1, e2, t) ->
          let op', ex_ty = symb_binop_of_cil op in
          (* != --->  (! (= )) *)
          if op' = Neq then
            FnUnop(Not,
                   FnBinop (Eq,
                            convert_cils ~subs:subs ~expect_ty:ex_ty e1,
                            convert_cils ~subs:subs ~expect_ty:ex_ty e2))
          else
            FnBinop (op',
                     convert_cils ~subs:subs ~expect_ty:ex_ty e1,
                     convert_cils ~subs:subs ~expect_ty:ex_ty e2)

        | Cil.Question (c, e1, e2, t) ->
          let c' = convert_cils ~expect_ty:Boolean c in
          FnQuestion (c',  convert_cils ~subs:subs e1,
                      convert_cils ~subs:subs e2)

        | Cil.CastE (t, e) ->
          let ty = type_of_ciltyp t in
          FnCastE (ty , convert_cils ~subs:subs ~expect_ty:ty e)

        | Cil.StartOf lv ->
          FnStartOf (skexpr_of_lval lv)


      and convert_offset =
        function
        | Cil.NoOffset -> []
        | Cil.Index (e, offset) ->
          ((convert_cils e)::(convert_offset offset))
        | Cil.Field _ -> []

      and convert_offsets offsets_list =
        List.fold_left
          (fun acc x -> acc@[convert_cils x]) [] offsets_list


      and skexpr_of_lval ((host, offset) : Cil.lval) =
        match convert_offset offset with
        (**
            An empty list only means there is no offset in the offset part
            of the Cil.lval, but the offset might still in the expression
            if it is a Cil memory access.
        *)
        | [] ->
          let vo, ofs_li = analyze_host host in
          begin
            match vo with
            | Some vi ->
              mkVarExpr ~offsets:(convert_offsets ofs_li) (var_of_vi vi)
            | None -> failhere __FILE__ "skexpr_of_lval" "Is it an lval?"
          end

        | new_off_list ->
          let vo, prev_offs_list =  analyze_host host in
          let off_list = (convert_offsets prev_offs_list)@new_off_list in
          let vi_to_expr =
            match vo with
            | None ->
              (** Anonymous function with type *)
              (fun t x -> FnApp (t, None, off_list))
            | Some vi ->
              (fun t x -> x (var_of_vi vi))
          in
          let t =  Cil.typeOfLval (host,offset) in
          vi_to_expr
            (type_of_ciltyp t)
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
                     FnVariable (var_of_vi (VS.find_by_id k state_vars))
                   with Not_found -> FnVariable
                                       (var_of_vi (VS.find_by_id k all_vars))
                 in
                 (cur_v, convert e))
              subs
          in
          let complete_state =
            VS.fold
              (fun state_vi l ->
                 let state_var = var_of_vi state_vi in
                 l@[
                   if IM.mem state_var.vid state
                   then IM.find state_var.vid state
                   else (FnVariable state_var, mkVarExpr state_var)])
              state_vars []
          in
          FnLetExpr complete_state

        | Let (v, e, cont, i, loc) ->
          let rec cur_v (v : lhs) =
            match v with
            | LhVar vi -> FnVariable (var_of_vi vi)
            | LhTuple vil -> FnTuple (varset_of_vs vil)
            | LhElem (a, i) ->
              let fv = cur_v a in
              FnArray(fv, convert i)
          in
          FnLetIn ([(cur_v v, convert e)], convert_letin cont)


        | LetCond (c, let_if, let_else, let_cont, loc) ->
          if is_empty_state let_cont then
            FnLetExpr [(FnTuple (varset_of_vs state_vars),
                        FnCond (convert c,
                                convert_letin let_if,
                                convert_letin let_else))]
          else
            FnLetIn ( [(FnTuple (varset_of_vs state_vars),
                        FnCond (convert c,
                                convert_letin let_if,
                                convert_letin let_else))],
                      convert_letin let_cont)

      in

      let index, (ilet, gexpr, ulet) = figu in

      let iletin = convert_letin ilet in
      let uletin = convert_letin ulet in
      (** TODO implement records to manage index *)
      let gskexpr = convert gexpr in
      sketch <- Some (optims (convert_letin func),
                      (index, (iletin, gskexpr, uletin)));

    method get_sketch = sketch
    method get_uses_global_bounds = uses_global_bound
  end

(** Defines the kind of constants we can accept a initialization
    parameters.
    Translates a Cil.exp into a FnetchTypes.fnExpr.
*)

let rec conv_init_expr expected_type (cil_exp : Cil.exp) =
  match cil_exp with
  | Cil.Const c -> Some (convert_const expected_type c)
  | Cil.Lval (h, o) ->
    (match h with
     | Cil.Var vi ->
       (match c_constant vi.Cil.vname with
        | Some skconst -> Some (FnConst skconst)
        | None ->
          match o with
          | Cil.NoOffset -> Some (FnVar (FnVariable (var_of_vi vi)))
          | Cil.Index (e, o) ->
            begin
              match conv_init_expr Integer e with
              | Some se -> Some (FnVar (FnArray (FnVariable (var_of_vi vi), se)))
              | None -> None
            end
          | _ -> None)
     | Cil.Mem (Cil.BinOp (_, Cil.Lval ((Cil.Var vi), Cil.NoOffset), e,_)) ->
       (match conv_init_expr Integer e with
        | Some e_index -> Some (FnVar (FnArray ((FnVariable (var_of_vi vi)), e_index)))
        | _ -> None)
     | _ -> None)
  | _ -> None


(** Transform the converted sketch to a loop body and a join sketch *)

let rec make_conditional_guards initial_vs letin_form =
  match letin_form with
  | FnLetIn (bindings, body) ->
    let new_bindings, new_state_vars = mk_cg bindings initial_vs in
    let new_body, state_vars' =
      make_conditional_guards new_state_vars body in
    FnLetIn (new_bindings, new_body), state_vars'

  | FnLetExpr bindings ->
    let new_bindings, new_state_vars = mk_cg bindings initial_vs in
    FnLetExpr new_bindings, new_state_vars

  | _ -> letin_form, initial_vs
and mk_cg bindings vs =
  (List.fold_left
     (fun acc binding -> acc @ [mk_cg_binding vs binding]) [] bindings), vs

and mk_cg_binding vs ((var, expr) : fnLVar * fnExpr) =
  (var, expr)

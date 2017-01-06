open Utils
open Cil

open SketchTypes


let zero = Const (CInt64 (0L, IInt, None))
let one = Const (CInt64 (1L, IInt, None))
let cil_true = Const (CInt64 (1L, IBool, None))
let cil_false = Const (CInt64 (0L, IBool, None))
let singl_init x = SingleInit x

let sk_zero = SkConst (CInt 0)
let sk_one = SkConst (CInt 1)
let sk_true = SkConst (CBool true)
let sk_false = SkConst (CBool false)

let cil_int = TInt (IInt, [])
let cil_bool = TInt (IBool, [])
let cil_int_array = TArray (cil_int, None, [])
let cil_bool_array = TArray (cil_bool, None, [])

(* Warning : default is zero !*)
let make_int_varinfo  ?(init = zero) varname =
  makeVarinfo false varname ~init:(singl_init init) cil_int

let make_bool_varinfo ?(init = cil_true) varname =
  makeVarinfo false varname ~init:(singl_init init) cil_bool

let make_int_array_varinfo varname =
  makeVarinfo false varname cil_int_array

let make_bool_array_varinfo vname =
  makeVarinfo false vname cil_bool_array

let cil_exp_of_vi vi =
  Lval (Var vi, NoOffset)

let var v = SkVarinfo v
let evar v = SkVar (var v)

let make_var ?(offsets = []) typ vname =
  match typ with
  | "int" ->
    let vi = make_int_varinfo vname in vi, mkVar vi, mkVarExpr vi
  | "bool" ->
    let vi = make_bool_varinfo vname in vi, mkVar vi, mkVarExpr vi
  | "int array" ->
    let vi = make_int_array_varinfo vname in
    vi, mkVar ~offsets:offsets vi, mkVarExpr ~offsets:offsets vi
  | "bool array" ->
    let vi = make_bool_array_varinfo vname in
    vi, mkVar ~offsets:offsets vi, mkVarExpr ~offsets:offsets vi
  (** Int by default *)
  | _->
    let vi = make_int_varinfo vname in vi, mkVar vi, mkVarExpr vi

let rec vi_of_var =
  function
  | SkVarinfo vi -> Some vi
  | SkArray (v, _) -> vi_of_var v
  | SkTuple vs -> None

(* Sketch type expression *)
let sk_tail_state =
  SkLetExpr ([])

let increment_all_indexes index_exprs =
  IM.fold
    (fun vid expr ->
       IM.add vid (SkBinop (Plus, expr, sk_one))
    )
    index_exprs
    IM.empty

let _s vil = VS.of_list vil
let ( $ ) vi e = SkVar (SkArray ((SkVarinfo vi), e))
let _b e1 op e2 = SkBinop (op, e1, e2)
let _u op e1 = SkUnop (op, e1)
let _Q c e1 e2 = SkQuestion (c, e1, e2)
let _let el = SkLetExpr el
let _letin el l = SkLetIn (el, l)

class variableManager vi_list =
  let smap =
    (List.fold_left
       (fun sm vi -> SM.add vi.vname vi sm)
       SM.empty vi_list)
  in
  object (self)
    val mutable vi_map = smap
    val vs = VS.of_list vi_list
    method add vi = vi_map <- (SM.add vi.vname vi vi_map)
    method vi name = SM.find name vi_map
    method var name = SkVarinfo (SM.find name vi_map)
    method expr name = SkVar (SkVarinfo (SM.find name vi_map))
    method get_vs = vs
  end
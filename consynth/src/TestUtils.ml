open Utils
open Cil

module T = SketchTypes


let zero = Const (CInt64 (0L, IInt, None))
let one = Const (CInt64 (1L, IInt, None))
let cil_true = Const (CInt64 (1L, IBool, None))
let cil_false = Const (CInt64 (0L, IBool, None))
let singl_init x = SingleInit x

let sk_zero = T.SkConst (T.CInt 0)
let sk_one = T.SkConst (T.CInt 1)
let sk_true = T.SkConst (T.CBool true)
let sk_false = T.SkConst (T.CBool false)

let cil_int = TInt (IInt, [])
let cil_bool = TInt (IBool, [])

(* Warning : default is zero !*)
let make_int_varinfo  ?(init = zero) varname =
  makeVarinfo false varname ~init:(singl_init init) cil_int

let make_bool_varinfo ?(init = cil_true) varname =
  makeVarinfo false varname ~init:(singl_init init) cil_bool

let exp_skvar vi =
  T.SkVar (T.SkVarinfo vi)
let cil_exp_of_vi vi =
  Lval (Var vi, NoOffset)

let rec vi_of_var =
  function
  | T.SkState -> None
  | T.SkVarinfo vi -> Some vi
  | T.SkArray (v, _) -> vi_of_var v

(* Sketch type expression *)
let sk_tail_state =
  T.SkLetExpr ([(T.SkState, T.SkVar (T.SkState))])

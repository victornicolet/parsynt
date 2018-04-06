open Utils
open Cil
open PpTools
open FuncTypes


let zero = Const (CInt64 (0L, IInt, None))
let one = Const (CInt64 (1L, IInt, None))
let cil_true = Const (CInt64 (1L, IBool, None))
let cil_false = Const (CInt64 (0L, IBool, None))
let singl_init x = SingleInit x

let sk_zero = FnConst (CInt 0)
let sk_one = FnConst (CInt 1)
let sk_true = FnConst (CBool true)
let sk_false = FnConst (CBool false)

let cil_int = TInt (IInt, [])
let cil_bool = TInt (IBool, [])
let cil_int_array = TArray (cil_int, None, [])
let cil_bool_array = TArray (cil_bool, None, [])
let cil_int_int_array = TArray (cil_int_array, None, [])
(* Warning : default is zero !*)
let make_int_varinfo  ?(init = zero) varname =
  makeVarinfo false varname ~init:(singl_init init) cil_int

let make_bool_varinfo ?(init = cil_true) varname =
  makeVarinfo false varname ~init:(singl_init init) cil_bool

let make_int_array_varinfo varname =
  makeVarinfo false varname cil_int_array

let make_int_int_array_varinfo varname =
  makeVarinfo false varname cil_int_int_array

let make_bool_array_varinfo vname =
  makeVarinfo false vname cil_bool_array

let cil_exp_of_vi vi =
  Lval (Var vi, NoOffset)

let var v = FnVarinfo v
let evar v = FnVar (var v)

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
  | FnVarinfo vi -> Some vi
  | FnArray (v, _) -> vi_of_var v
  | FnTuple vs -> None

(* Fnetch type expression *)
let sk_tail_state =
  FnLetExpr ([])

let increment_all_indexes index_exprs =
  IM.fold
    (fun vid expr ->
       IM.add vid (FnBinop (Plus, expr, sk_one))
    )
    index_exprs
    IM.empty

let _s vil = VS.of_list vil
let ( $ ) vi e = FnVar (FnArray ((FnVarinfo vi), e))
let ( $$ ) vi (e1, e2) = FnVar (FnArray ((FnArray ((FnVarinfo vi), e1)), e2))
let _ci i = FnConst (CInt i)
let _cb b = FnConst (CBool b)
let _b e1 op e2 = FnBinop (op, e1, e2)
let _u op e1 = FnUnop (op, e1)
let _Q c e1 e2 = FnQuestion (c, e1, e2)
let _let el = FnLetExpr el
let _letin el l = FnLetIn (el, l)
(* some functions lifted to host language *)
let fplus e1 e2 = _b e1 Plus e2
let ftimes e1 e2 = _b e1 Times e2
let fmin e1 e2 = _b e1 Min e2
let fmax e1 e2 = _b e1 Max e2
let fand e1 e2 = _b e1 And e2
let fgt e1 e2 = _b e1 Gt e2
let flt e1 e2 = _b e1 Lt e2
let fneg e1 = _u Neg e1
let fnot e1 = _u Not e1

let make_empty_fundec () =
  {
    svar = make_int_varinfo "empty_function";
    sformals = [];
    slocals = [];
    sbody = {bstmts = []; battrs = []};
    smaxstmtid = None;
    smaxid = 0;
    sallstmts = [];
  }

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
    method var name = FnVarinfo (SM.find name vi_map)
    method expr name = FnVar (FnVarinfo (SM.find name vi_map))
    method get_vs = vs
  end

class namedVariables =
  object (self)
    val vars : Cil.varinfo Sets.SH.t = Sets.SH.create 32
    method add_vars_by_name l =
     List.iter self#add_var_name l
    method add_var_name (varname, typname) =
      let var =
        match typname with
        | "int" -> make_int_varinfo varname
        | "bool" -> make_bool_varinfo varname
        | "int array" -> make_int_array_varinfo varname
        | "bool array" -> make_bool_array_varinfo varname
        | _ -> failhere __FILE__ "add_var_name" "Bad type."
      in
      Sets.SH.add vars varname var
    method get s = Sets.SH.find vars s
  end

(*  Pretty printing passed/error/failure messages for tests. *)
let msg_color tcolor bcolor msg =
  Format.printf "%s%s%s%s@." (color tcolor) (color bcolor) msg color_default

let msg_passed = msg_color "black" "b-green"
let msg_failed = msg_color "white" "b-red"

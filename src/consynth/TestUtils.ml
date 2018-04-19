open Utils
open PpTools
open FuncTypes


let sk_zero = FnConst (CInt 0)
let sk_one = FnConst (CInt 1)
let sk_true = FnConst (CBool true)
let sk_false = FnConst (CBool false)

(* Warning : default is zero !*)
let make_int_varinfo  varname =
  mkFnVar varname Integer

let make_bool_varinfo  varname =
  mkFnVar varname Boolean

let make_int_array_varinfo varname =
  mkFnVar varname (Vector(Integer, None))

let make_int_int_array_varinfo varname =
  mkFnVar varname (Vector(Vector(Integer,None),None))

let make_bool_array_varinfo vname =
  mkFnVar vname (Vector(Boolean, None))

let var v = FnVariable v
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
  | FnVariable vi -> Some vi
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

let _s vil = VarSet.of_list vil
let ( $ ) vi e = FnVar (FnArray ((FnVariable vi), e))
let ( $$ ) vi (e1, e2) = FnVar (FnArray ((FnArray ((FnVariable vi), e1)), e2))
let _ci i = FnConst (CInt i)
let _cb b = FnConst (CBool b)
let _b e1 op e2 = FnBinop (op, e1, e2)
let _u op e1 = FnUnop (op, e1)
let _Q c e1 e2 = FnCond (c, e1, e2)
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

class variableManager vi_list =
  let smap =
    (List.fold_left
       (fun sm vi -> SM.add vi.vname vi sm)
       SM.empty vi_list)
  in
  object (self)
    val mutable vi_map = smap
    val vs = VarSet.of_list vi_list
    method add vi = vi_map <- (SM.add vi.vname vi vi_map)
    method vi name = SM.find name vi_map
    method var name = FnVariable (SM.find name vi_map)
    method expr name = FnVar (FnVariable (SM.find name vi_map))
    method get_vs = vs
  end

class namedVariables =
  object (self)
    val vars : fnV Sets.SH.t = Sets.SH.create 32
    method add_vars_by_name l =
     List.iter self#add_var_name l
    method add_var_name (varname, typname) =
      let var =
        match typname with
        | "int" -> make_int_varinfo varname
        | "bool" -> make_bool_varinfo varname
        | "int_array" -> make_int_array_varinfo varname
        | "int_int_array" -> make_int_int_array_varinfo varname
        | "bool_array" -> make_bool_array_varinfo varname
        | _ -> failhere __FILE__ "add_var_name" "Bad type."
      in
      Sets.SH.add vars varname var
    method get s =
      try
        Sets.SH.find vars s
      with Not_found ->
        (Format.printf "Variable %s not found.@." s;
         raise Not_found)
  end

(*  Pretty printing passed/error/failure messages for tests. *)
let msg_color tcolor bcolor msg =
  Format.printf "%s%s%s%s@." (color tcolor) (color bcolor) msg color_default

let msg_passed = msg_color "black" "b-green"
let msg_failed = msg_color "white" "b-red"


(* Using S-Expressions *)
open Sexplib.Sexp
module S = Sexplib.Type

let vardefs defstring =
  let nv = new namedVariables in
  let defs = parse defstring in
  (match defs with
   | Done (sexpdefs, _) ->
     (match sexpdefs with
      | S.List l ->
        List.iter
          (fun pair -> match pair with
             | S.List [S.Atom a; S.Atom b] -> nv#add_var_name (a,b)
             | S.Atom a -> failwith "Definition must be (name type)"
             | _ -> failwith "Bad definitions.") l
      | S.Atom k -> print_endline k ;failwith "Bad definitions. Must be ((name type) ...)")
   | _ -> failwith "Unexpected");
  nv


let rec const_string a =
    try
      _ci (int_of_string a)
    with e ->
        match a with
        | "true" -> _cb true
        | "false" -> _cb false
        | _ -> raise e


and constr_expr vardefs e =
    match e with
    | S.List (t::tl) ->
      (
        let args = List.map (constr_expr vardefs) tl in
        match List.length args with
        | 3 ->
          (match t with
           | Atom s when s = "?" -> _Q (args >> 0) (args >> 1) (args >> 2)
           | _ -> failwith "App 3 error")
        | 2 ->
          (let op =
             match t with
             | Atom s ->
               (match s with
               | "+" -> Plus | "-" -> Minus | "max" -> Max | "min" -> Min
               | ">" -> Gt | "<" -> Lt | "<=" -> Le | ">=" -> Ge | "=" -> Eq
               | "&&" -> And | "||" -> Or
               | _ -> failwith "Binop error.")
             | _ -> failwith "App 2 error"
           in
           _b (args >> 0) op (args >> 1))
        | 1 ->
          (let op =
             match t with
             | Atom s ->
               (match s with |"-" -> Neg | "!" -> Not | _ -> failwith "Unop error.")
             | _ -> failwith "App 1 error"
           in
           _u op (args >> 0))
         | _ -> failwith "App n")
    | S.Atom a ->
      (try
         const_string a
      with _ ->
        let aparts = Str.split (Str.regexp "\#") a in
        FnVar (List.fold_left
                 (fun  v offset -> FnArray (v, expression vardefs offset))
                 (var (vardefs#get (List.hd aparts)))
                 (List.tl aparts)))
    | _ -> failwith "toplevel error"


and expression vardefs string_expression =
  let rec cstr_expr e =
    match parse string_expression with
    | Done (sexpr, _) ->
      constr_expr vardefs sexpr
    | _ ->
      try
        const_string string_expression
      with _ ->
        failwith "Couldn't terminate parsing."
  in
  cstr_expr string_expression


let make_context vardefs defstring : context =
  let tovars atomlist =
    match atomlist with
    | S.List l ->
      VarSet.of_list
        (List.map
           (fun maybe_atom ->
              match maybe_atom with
              | S.Atom s -> vardefs#get s
              | _ -> failhere __FILE__ "context" "Expected atom.")
           l)
    | _ -> failhere __FILE__ "context" "Expected list."
  in
  let toexprs exprlist =
    match exprlist with
    | S.List l ->
      ES.of_list
        (List.map
           (fun maybe_expr -> constr_expr vardefs maybe_expr)
           l)
    | _ -> failhere __FILE__ "context" "Expected list."
  in
  let defs = parse defstring in
  (match defs with
   | Done (sexpdefs, _) ->
     (match sexpdefs with
      | S.List l ->
        (if List.length l != 5 then
           failhere __FILE__ "context" "context has 5 members."
         else
           {
             state_vars = tovars (l >> 0);
             index_vars = tovars (l >> 1) ;
             used_vars = tovars (l >> 2);
             all_vars = tovars (l >> 3);
             costly_exprs = toexprs (l >> 4);
           })
        | S.Atom k -> print_endline k;
         failhere __FILE__ "context" "Bad context definition.")
   | _ -> failwith "Unexpected")

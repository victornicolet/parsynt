(**
   This file is part of Parsynt.

    Parsynt is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Parsynt is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Parsynt.  If not, see <http://www.gnu.org/licenses/>.
*)

open Beta
open Fn
open Utils

let sk_zero = FnConst (CInt 0)

let sk_one = FnConst (CInt 1)

let sk_true = FnConst (CBool true)

let sk_false = FnConst (CBool false)

(* Warning : default is zero !*)
let make_int_varinfo varname = mkFnVar varname Integer

let make_bool_varinfo varname = mkFnVar varname Boolean

let make_int_array_varinfo varname = mkFnVar varname (Vector (Integer, None))

let make_int_int_array_varinfo varname = mkFnVar varname (Vector (Vector (Integer, None), None))

let make_bool_array_varinfo vname = mkFnVar vname (Vector (Boolean, None))

let var v = FnVariable v

let evar v = FnVar (var v)

let make_var ?(offsets = []) typ vname =
  match typ with
  | "int" ->
      let vi = make_int_varinfo vname in
      (vi, mkVar vi, mkVarExpr vi)
  | "bool" ->
      let vi = make_bool_varinfo vname in
      (vi, mkVar vi, mkVarExpr vi)
  | "int array" ->
      let vi = make_int_array_varinfo vname in
      (vi, mkVar ~offsets vi, mkVarExpr ~offsets vi)
  | "bool array" ->
      let vi = make_bool_array_varinfo vname in
      (vi, mkVar ~offsets vi, mkVarExpr ~offsets vi)
  (* Int by default *)
  | _ ->
      let vi = make_int_varinfo vname in
      (vi, mkVar vi, mkVarExpr vi)

let rec vi_of_var = function FnVariable vi -> Some vi | FnArray (v, _) -> vi_of_var v

let increment_all_indexes index_exprs =
  IM.fold (fun vid expr -> IM.set vid (FnBinop (Plus, expr, sk_one))) index_exprs IM.empty

let _s vil = VarSet.of_list vil

let ( $ ) vi e = FnVar (FnArray (FnVariable vi, e))

let ( $$ ) vi (e1, e2) = FnVar (FnArray (FnArray (FnVariable vi, e1), e2))

let _ci i = FnConst (CInt i)

let _cb b = FnConst (CBool b)

let _b e1 op e2 = FnBinop (op, e1, e2)

let _u op e1 = FnUnop (op, e1)

let _Q c e1 e2 = FnCond (c, e1, e2)

let _let el = wrap_state el

let _letin el l = FnLetIn (el, l)

let _inrec r x = FnRecordMember (evar r, x.vname)

let _self r x = (var x, FnRecordMember (evar r, x.vname))

(* some functions lifted to host language *)
let fplus e1 e2 = _b e1 Plus e2

let fminus e1 e2 = _b e1 Minus e2

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
    List.fold_left (fun sm vi -> Base.Map.set ~key:vi.vname ~data:vi sm) SM.empty vi_list
  in
  object
    val mutable vi_map : VarSet.elt SM.t = smap

    val vs = VarSet.of_list vi_list

    method add vi = vi_map <- SM.set vi.vname vi vi_map

    method vi name = SM.find name vi_map

    method var name = Option.map mkVarExpr (SM.find name vi_map)

    method expr name = Option.map mkVarExpr (SM.find name vi_map)

    method get_vs = vs
  end

class namedVariables =
  object (self)
    val vars : fnV SH.t = SH.create 32

    method add_vars_by_name l = List.iter self#add_var_name l

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
      SH.add vars varname var

    method get s =
      try SH.find vars s
      with _ ->
        Format.printf "Variable %s not found.@." s;
        raise Not_found
  end

(*  Pretty printing passed/error/failure messages for tests. *)
let msg_color _ _ msg = Format.printf "%s@." msg

let msg_passed = msg_color "black" "b-green"

let msg_failed = msg_color "white" "b-red"

(* Using S-Expressions *)
open Sexplib.Sexp
module S = Sexplib.Type

let vardefs defstring =
  let nv = new namedVariables in
  let defs = parse defstring in
  (match defs with
  | Done (sexpdefs, _) -> (
      match sexpdefs with
      | S.List l ->
          List.iter
            (fun pair ->
              match pair with
              | S.List [ S.Atom a; S.Atom b ] -> nv#add_var_name (a, b)
              | S.Atom _ -> failwith "Definition must be (name type)"
              | _ -> failwith "Bad definitions.")
            l
      | S.Atom k ->
          print_endline k;
          failwith "Bad definitions. Must be ((name type) ...)")
  | _ -> failwith "Unexpected");
  nv

let rec const_string a =
  try _ci (int_of_string a)
  with e -> ( match a with "true" -> _cb true | "false" -> _cb false | _ -> raise e)

and constr_expr vardefs e =
  match e with
  | S.List (t :: tl) -> (
      let args = List.map (constr_expr vardefs) tl in
      match List.length args with
      | 3 -> (
          match t with
          | Atom s when s = "?" -> _Q (args >> 0) (args >> 1) (args >> 2)
          | _ -> failwith "App 3 error")
      | 2 ->
          let op =
            match t with
            | Atom s -> (
                match s with
                | "+" -> Plus
                | "-" -> Minus
                | "max" -> Max
                | "min" -> Min
                | ">" -> Gt
                | "<" -> Lt
                | "<=" -> Le
                | ">=" -> Ge
                | "=" -> Eq
                | "&&" -> And
                | "||" -> Or
                | _ -> failwith "Binop error.")
            | _ -> failwith "App 2 error"
          in
          _b (args >> 0) op (args >> 1)
      | 1 ->
          let op =
            match t with
            | Atom s -> ( match s with "-" -> Neg | "!" -> Not | _ -> failwith "Unop error.")
            | _ -> failwith "App 1 error"
          in
          _u op (args >> 0)
      | _ -> failwith "App n")
  | S.Atom a -> (
      try const_string a
      with _ ->
        let aparts = Str.split (Str.regexp "\\#") a in
        FnVar
          (List.fold_left
             (fun v offset -> FnArray (v, expression vardefs offset))
             (var (vardefs#get (List.hd aparts)))
             (List.tl aparts)))
  | _ -> failwith "toplevel error"

and expression vardefs string_expression =
  let cstr_expr _ =
    match parse string_expression with
    | Done (sexpr, _) -> constr_expr vardefs sexpr
    | _ -> ( try const_string string_expression with _ -> failwith "Couldn't terminate parsing.")
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
    | S.List l -> ES.of_list (List.map (fun maybe_expr -> constr_expr vardefs maybe_expr) l)
    | _ -> failhere __FILE__ "context" "Expected list."
  in
  let defs = parse defstring in
  match defs with
  | Done (sexpdefs, _) -> (
      match sexpdefs with
      | S.List l ->
          if List.length l != 5 then failhere __FILE__ "context" "context has 5 members."
          else
            {
              state_vars = tovars (l >> 0);
              index_vars = tovars (l >> 1);
              used_vars = tovars (l >> 2);
              all_vars = tovars (l >> 3);
              costly_exprs = toexprs (l >> 4);
            }
      | S.Atom k ->
          print_endline k;
          failhere __FILE__ "context" "Bad context definition.")
  | _ -> failwith "Unexpected"

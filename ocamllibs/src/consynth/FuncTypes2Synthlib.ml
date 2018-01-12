(**
   This file is part of Parsynt.

   Author: Victor Nicolet <victorn@cs.toronto.edu>

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
open Cil
open FuncTypes
open FPretty
open List
open Synthlib2ast
open Synthlib
open Utils


let rec of_letform terminal_expr =
    let _aux  (var, expr) =
      match var with
      | FnVarinfo v ->
        let sort = sort_of_varinfo v in
        (v.vname, sort, to_term ~texpr:terminal_expr expr)
      | _ -> failhere __FILE__ "to_term"
               "Unsupported left hand side in binding."
    in
    function
      | FnLetIn (velist, cont) ->
        SyLet(map _aux velist, of_letform terminal_expr cont)
      | FnLetExpr velist ->
        SyLet(map _aux velist, terminal_expr)



and  to_term ?(texpr=SyLiteral(SyBool true)) =
  let rec of_var fnvar =
    match fnvar with
    | FnVarinfo vi -> SyId vi.vname
    | FnArray(v,e) -> of_var v
    | FnTuple _ -> failhere __FILE__ "to_term" "Tuples not supported."
  in
  let of_const cst =
    match cst with
    | CInt i -> SyInt i
    | CInt64 il -> SyInt (Int64.to_int il)
    | CReal r -> SyReal r
    | CBool b -> SyBool b
    | CString s -> SyString s
    | _ -> failhere __FILE__ "to_term" "Unsupported constant."
  in
  function
  | FnVar v ->of_var v
  | FnConst c -> SyLiteral (of_const c)
  | FnBinop(op, e1, e2) ->
    SyApp(string_of_symb_binop op,
          [to_term ~texpr:texpr e1; to_term ~texpr:texpr e2])
  | FnUnop(op, e) -> SyApp(string_of_symb_unop op, [to_term ~texpr:texpr e])
  | FnQuestion(c,e1,e2) -> SyApp("ite", map (to_term ~texpr:texpr) [c;e1;e2])
  | FnApp(_,maybe_v, args) ->
    (try
      let v = check_option maybe_v in
      SyApp(v.vname, map (to_term ~texpr:texpr) args)
    with Failure s -> failhere __FILE__ "to_term terminal_expr" "Unsupported function.")
  | _ -> failhere __FILE__ "to_term" "Unsupported construct."


(* The inverse conversion: from terms to expressions. *)

let to_fnconst =
  function
  | SyInt i -> FnConst (CInt i)
  | SyReal r -> FnConst (CReal r)
  | SyBool b -> FnConst (CBool b)

let to_fnexpr vars  =
  let rec _fnexpr =
    function
    | SyId v ->
      (try
        let vi = VS.find_by_name v vars in
        FnVar (FnVarinfo vi)
      with Not_found ->
        failhere __FILE__ "to_fnexpr" "Unknown variable.")
    | SyLiteral lit -> to_fnconst lit
    | SyApp (fname, args) ->
      let fargs = map _fnexpr args in
      let obinop, ounop =
        symb_binop_of_fname fname, symb_unop_of_fname fname
      in
      begin
        match obinop, ounop with
        | Some binop, _ ->
          FnBinop(binop, hd fargs, hd (tl fargs))
        | _ , Some unop ->
          FnUnop(unop, hd fargs)
        | None, None ->
          (* Dummy function for now. TODO: need a mapping from function names
             to their types for unrecognized functions.*)
          FnApp(Integer, None, fargs)
      end
    | SyLet(bindings, interm) ->

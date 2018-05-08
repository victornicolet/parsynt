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

open FuncTypes
open FPretty
open List
open Synthlib2ast
open Synthlib
open Utils

let rec  to_term ?(texpr=SyLiteral(SyBool true)) =
  let _binding  (var, expr) =
    match var with
    | FnVariable v ->
      let sort = sort_of_varinfo (cil_varinfo v) in
      (v.vname, sort, to_term ~texpr:texpr expr)
    | _ -> failhere __FILE__ "to_term"
             "Unsupported left hand side in binding."
  in
  let rec of_var fnvar =
    match fnvar with
    | FnVariable vi -> SyId vi.vname
    | FnArray(v,e) -> of_var v
    | FnRecord _ -> failhere __FILE__ "to_term" "Records not supported."
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
  | FnLetIn (velist, cont) ->
    SyLet(map _binding velist, to_term ~texpr:texpr cont)
  | FnLetExpr velist ->
    SyLet(map _binding velist, texpr)
  | FnVar v ->of_var v
  | FnConst c -> SyLiteral (of_const c)
  | FnBinop(op, e1, e2) ->
    SyApp(string_of_symb_binop op,
          [to_term ~texpr:texpr e1; to_term ~texpr:texpr e2])
  | FnUnop(op, e) -> SyApp(string_of_symb_unop op, [to_term ~texpr:texpr e])
  | FnCond(c,e1,e2) -> SyApp("ite", map (to_term ~texpr:texpr) [c;e1;e2])
  | FnApp(_,maybe_v, args) ->
    (try
      let v = check_option maybe_v in
      SyApp(v.vname, map (to_term ~texpr:texpr) args)
     with Failure s ->
       failhere __FILE__ "to_term terminal_expr" "Unsupported function.")
  | _ -> failhere __FILE__ "to_term" "Unsupported construct."


(* The inverse conversion: from terms to expressions. *)

let to_fnconst =
  function
  | SyInt i -> FnConst (CInt i)
  | SyReal r -> FnConst (CReal r)
  | SyBool b -> FnConst (CBool b)
  | SyString s -> FnConst (CString s)
  | _ -> FnConst (CString "bitvector_or_enum")

let to_fnexpr vars =
  let rec _binding (v,t,e) =
    let vi = VarSet.find_by_name vars v in
    (FnVariable vi, _fnexpr e)
  and  _fnexpr =
    function
    | SyId v ->
      (try
        let vi = VarSet.find_by_name vars v in
        FnVar (FnVariable vi)
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
      FnLetIn(map _binding bindings, _fnexpr interm)
  in _fnexpr

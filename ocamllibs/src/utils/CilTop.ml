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

open Sets
open Format
open Cil

let psprint80 f x = Pretty.sprint 80 (f () x)
let ppe e = print_endline (psprint80 Cil.dn_exp e)
let ppt t = print_endline (psprint80 Cil.d_type t)
let pps s = print_endline (psprint80 Cil.dn_stmt s)
let pplv lv = print_endline (psprint80 Cil.dn_lval lv)
let ppv v = print_endline v.vname
let ppi i = print_endline ("[instr] "^(psprint80 Cil.dn_instr i))
let ppbk blk = List.iter pps blk.bstmts
let ppofs offs = print_endline (psprint80 (Cil.d_offset Pretty.nil) offs)


let fppe fmt e = fprintf fmt "%s" (psprint80 Cil.dn_exp e)
let fppt fmt t = fprintf fmt "%s" (psprint80 Cil.d_type t)
let fpps fmt s = fprintf fmt "%s" (psprint80 Cil.dn_stmt s)
let fplv fmt lv = fprintf fmt "%s" (psprint80 Cil.dn_lval lv)
let fppv fmt v = fprintf fmt "%s" v.vname
let fppi fmt i = fprintf fmt "%s" (psprint80 Cil.dn_instr i)
let fppbk fmt blk = List.iter (fpps fmt) blk.bstmts
let fppofs fmt offs = fprintf fmt "%s" (psprint80 (Cil.d_offset Pretty.nil) offs)


let is_cil_temp vi =
  false

let is_literal_zero = function
  | Const (CInt64 (0L, _, _)) -> true
  | _ -> false


let add_instr stmt instr =
  match stmt.skind with
  | Instr il ->
    {stmt with skind = Instr (il @ instr)}
  | _ ->
    eprintf "Instruction not added to non-instruction list statement.";
    failwith "add_instr"

let add_stmt block stmt =
  { block with bstmts = block.bstmts @ stmt }

let add_loop_stmt loop stmt =
  match loop.skind with
  | Loop(b, x, y, z) ->
    {loop with skind = Loop(add_stmt b stmt, x, y ,z)}
  | _ -> loop

let extract_block loop : block =
  match loop.skind with
  | Loop(b, _, _ ,_ ) -> b
  | Block b -> b
  | _ ->
    failwith "loop_bstmt takes only loops as arg"


let make_block_stmt stmts =
  mkStmt(Block(mkBlock(stmts)))

let replace_loop_block loop nb =
  match loop.skind with
  | Loop(b, loc, os, os') ->
    {loop with skind = Loop(nb, loc, os, os')}
  | _ -> failwith "Not a loop in replace loop stmts."


(* Reaching definitions are a triple where the first
   two elements are not useful to us.p*)
let simplify_rds rdef =
  match rdef with
  | Some (_,_, setXhash) -> Some setXhash
  | None -> None


let neg_exp (exp : Cil.exp) =
  match exp with
  | UnOp (LNot, b, _) -> b
  | UnOp (Neg, x, _) -> x
  | _ -> UnOp (LNot, exp, TInt (IBool, []))

let is_like_array (vi : Cil.varinfo) =
  match vi.vtype with
  | TPtr _ | TArray _ -> true
  | _ -> false

let is_like_bool =
  function
  | IBool -> true
  | _ -> false

type simple_types =
  | BOOL
  | INT
  | FLOAT

let simple_type typename =
  match typename with
  | INT -> TInt (IInt, [])
  | BOOL -> TInt (IBool, [])
  | FLOAT -> TFloat (FFloat, [])

let simple_fun_type rettype_name args_typ_names =
  TFun (simple_type rettype_name,
        Some (List.map (fun s -> ("x", simple_type s, [])) args_typ_names),
        false, [])

let fun_ret_type tfunc =
  match tfunc with
  | TFun (ret_typ, _, _, _) -> Some ret_typ
  | _ -> None

let rec is_of_bool_type vitype =
  match vitype with
  | TInt (ityp, _) -> is_like_bool ityp
  | f ->
    (match fun_ret_type f with
     | Some ftyp -> is_of_bool_type ftyp
     | None -> false )

let is_of_real_type vitype =
  match vitype with
  | TFloat _ -> true
  | f -> (match fun_ret_type f with Some (TFloat _) -> true | _-> false)

let rec is_of_int_type vitype =
  match vitype with
  | TInt _ -> not (is_of_bool_type vitype)
  | f -> (match fun_ret_type f with Some x -> is_of_real_type x
                                  | None -> false)

let combine_expression_option op e1 e2 t=
  match e1, e2 with
  | Some e1, Some e2 -> Some (BinOp (op, e1, e2, t))
  | Some e1, None -> Some e1
  | None, Some e2 -> Some e2
  | None, None -> None

let gen_var_with_suffix vi suffix =
  {vi with vname = vi.vname^suffix}

let gen_var_with_prefix vi prefix =
  {vi with vname = prefix^vi.vname}

let change_var_typ vi new_typ =
  { vi with vtype = new_typ }

(* Get all the children statement ids of a statement *)
class statementIdsCollector hashids = object
  inherit nopCilVisitor
  val mutable stmt_ids = IS.empty
  method vstmt (s: stmt) =
    IH.add hashids s.sid s;
    DoChildren
end

let collect_sids stmt =
  let hashid = IH.create 10 in
  let visitor = new statementIdsCollector hashid in
  ignore(visitCilStmt visitor stmt);
  hashid

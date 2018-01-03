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
open Utils
open VariableAnalysis
open LoopsHelper
open Utils.PpTools
open Loops

module IM = Utils.IM
module Ct = CilTools

(**
   This modules performs some additonal analysis on the result
   of Findloops and returns a sorted list of loops. The loops should
   then be parallelized in the order of the output list.
*)

(**
    Given a loop body, extract all the array subscripts in array
    variables and return a mapping from variable ids to two lists of
    read,write array subscripts and the statement where they appear.
*)
let extract_subscripts (loop_body : block) ((r, w) : VS.t * VS.t) =
  let vars = VS.union r w in
  let rec from_stmt stmt =
    match stmt.skind with
      Instr il ->
        List.fold_left
          (fun acc instr ->
            acc@(from_instr stmt instr))
          []
          il

    | Block b
    | Loop (b, _, _, _) ->
       from_block b []

    | Switch (e, b, _, _) ->
       (from_block b  (from_expr stmt false e))

    | If (c, b1, b2, _) ->
       (from_block b1 (from_block b2 (from_expr stmt false c)))

    | Goto (stmt_ref, _) ->
      from_stmt !stmt_ref

    | TryFinally _
    | TryExcept _
    | Return _
    | ComputedGoto _
    | Break _
    | Continue _ ->
      (CilTools.pps stmt;
       failwith "Unsupported statement.")

  and from_block b acc_subs =
    List.fold_left
      (fun acc stmt ->
        acc@(from_stmt stmt))
      acc_subs
      b.bstmts

  and from_instr stmt instr =
    match instr with
    | Set (lv, e, t) ->
       (ex_from_lval stmt true lv)@(from_expr stmt false e)
    | Call (lvo, ef, args, t) ->
       (maybe_apply_default (ex_from_lval stmt true) lvo [])@
         (from_expr stmt false ef)@
       (List.fold_left (fun acc expr -> acc@(from_expr stmt false expr)) [] args)
    | Asm _  -> []


  and from_expr stmt on_left_hand expr =
    match expr with
    | Lval lv -> ex_from_lval stmt on_left_hand lv

    | CastE (_, e) | SizeOfE e | AlignOfE e
    | UnOp (_, e, _) ->
       from_expr stmt on_left_hand  e

    | BinOp (_, e1, e2, _) ->
       (from_expr stmt on_left_hand e1)@(from_expr stmt on_left_hand e2)

    | Question (c, e1, e2, _) ->
       (from_expr stmt on_left_hand e1)@
         (from_expr stmt on_left_hand e2)@
         (from_expr stmt on_left_hand c)

    | _ -> []

  and ex_from_lval stmt on_left_hand (host, off) =
       let offset = analyze_offset off in
       let main_host, offsets = analyze_host host in
       match main_host with
       | Some vi_host ->
         let offs = offsets@offset in
         (if List.length offs > 0 then
           [(vi_host.vid, offs, on_left_hand, stmt)]
         else [])
       | _ -> []
  in
  let subs_list = from_block loop_body [] in
  let init_map =
    VS.fold (fun vi map -> IM.add vi.vid ([],[]) map) vars IM.empty
  in
  let aggregate_subs =
    List.fold_left
      (fun imap (varid, offsets, on_lh, stmt) ->
        let read_offs, write_offs =
          try IM.find varid imap with Not_found -> ([], [])
        in
        let new_binding =
          if on_lh then (read_offs, write_offs@[(offsets, stmt)])
          else (read_offs@[(offsets, stmt)], write_offs)
        in
        IM.add varid new_binding imap
      )
      init_map
      subs_list
  in
  aggregate_subs


(**
   Condition for accepting loops :
   - no variable aliasing
   - no loop exit in the new_body
*)
let accept (lid : int) (loop : loop_info)  =
  let state = loop.lvariables.state_vars in
  (** If the state of the loop is empty, not need to parallelize it *)
  (not (VS.is_empty state)) &&
  (is_some loop.ligu) &&
  (** Verify that there is no aliasing in state variables *)
  (let loop_body = loop_body loop in
   VS.is_empty (VS.inter (aliased loop_body) state))


let transform (lid, loop) =
  let subscripts_map =
    extract_subscripts (loop_body loop) (loop_rwset loop) in
  loop


(**
    If (loop1 <= loop2) we will try to parallelize loop1 first because
    it is a simpler task (we order loops by their 'complexity')
*)
let compare_cl ((lid1, loop1) : int * loop_info) (lid2, loop2) =
  if loop1.lid = loop2.lcontext.parent_loop_id
  then -1
  else
    begin
      if loop2.lid = loop1.lcontext.parent_loop_id
      then 1
      else
        begin
          if (VS.cardinal (loop1.lvariables.state_vars)) <=
            (VS.cardinal (loop2.lvariables.state_vars))
          then 1
          else compare lid1 lid2
        end
    end


let transform_and_sort (loop_map : loop_info IM.t) =
  List.map transform
    (List.sort compare_cl
       (IM.bindings (IM.filter accept loop_map)))

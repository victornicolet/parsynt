open Cil
open Utils
open Utils.IMTools
open VariableAnalysis
open Findloops
open Findloops.Cloop
open LoopsHelper
open PpHelper

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

    | TryFinally _
    | TryExcept _
    | Return _
    | Goto _
    | ComputedGoto _
    | Break _
    | Continue _ -> failwith "Unsupported statement."

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
    | _ -> failwith "Unsupported instruction."

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
let accept (lid : int) (loop : Cloop.t)  =
  let _, state = loop.rwset in
  (**  Don't accept loops with breaks/exits in its body *)
  (not loop.has_breaks) &&
    (** If the state of the loop is empty, not need to parallelize it *)
    (not (VS.is_empty state)) &&
    (** Verify that there is no aliasing in state variables *)
    (let loop_body = mkBlock(loop.new_body) in
     VS.is_empty (VS.inter (aliased loop_body) state))


let transform (lid, loop) =
  let subscripts_map =
    extract_subscripts (mkBlock loop.new_body) loop.rwset in
  loop


(**
    If (loop1 <= loop2) we will try to parallelize loop1 first because
    it is a simpler task (we order loops by their 'complexity')
*)
let compare_cl ((lid1, loop1) : int * Cloop.t) (lid2, loop2) =
  if List.mem loop1.sid loop2.parent_loops
  then -1
  else
    begin
      if List.mem loop2.sid loop1.parent_loops
      then 1
      else
        begin
          if (VS.cardinal (state loop1)) <=
            (VS.cardinal (state loop2))
          then 1
          else compare lid1 lid2
        end
    end


let transform_and_sort (loop_map : Cloop.t IM.t) =
  List.map transform
    (List.sort compare_cl
       (IM.bindings (IM.filter accept loop_map)))
open Cil
open Utils
open Utils.IMTools
open VariableAnalysis
open Findloops
open Findloops.Cloop
open LoopsHelper

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
    read,write array subscripts and the statement where it appears.
*)
let extract_subscripts (loop_body : block) (vars : VS.t) =
  let from_stmt stmt =
    match stmt.skind with
      Instr il ->
        List.fold_left
          (fun ih instr -> IH.add )
    | Block b ->
    | Loop (b, _, _, _) ->

    | If (c, b1, b2, _) ->
    | Switch (e, b, _, _) ->
    | TryFinally _
    | TryExcept _
    | Return _
    | Goto _
    | ComputedGoto _
    | Break _
    | Continue _ -> failwith "Unsupported statement."

  and from_instr instr =
    match instr with
    | Set (lv, e, t) ->

    | Call (lvo, ef, args, t) ->
    | _ -> failwith "Unsupported instruction."

  and from_expr expr =
    match expr with
    | LVar (host, offset) ->
       let offset =
       let main_host, offsets = Ct.get_host_var lv in
       if Ct.is_like_array main_host
       then Some (vi.vid, Ct.g
    | CastE (_, e) | SizeOfE e | AlignOfE e
    | UnOp (_, e, _) ->

    | BinOp (_, e1, e2, _) ->

    | Question (c, e1, e2, _) ->

(**
   Condition for accepting loops :
   - no variable aliasing
   - no loop exit in the new_body
*)
let accept lid loop  =
  let _, state = loop.rwset in
  (**  Don't accept loops with breaks/exits in its body *)
  (not loop.has_breaks) &&
    (** If the state of the loop is empty, not need to parallelize it *)
    (not (VS.is_empty state)) &&
    (** Verify that there is no aliasing in state variables *)
    (let loop_body = mkBlock(loop.new_body) in
     VS.is_empty (VS.inter (aliased loop_body) state))


let transform loop = loop


(**
    If (loop1 <= loop2) we will try to parallelize loop1 first because
    it is a simpler task (we order loops by their 'complexity')
*)
let compare (lid1, loop1) (lid2, loop2) =
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


let transform (loop_map : Cloop.t IM.t) =
  List.map transform
    (List.sort compare (IM.bindings (IM.filter accept loop_map)))

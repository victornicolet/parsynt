open Cil
open Utils
open Utils.IMTools
open VariableAnalysis
open Findloops
open Findloops.Cloop
open LoopsHelper

module IM = Utils.IM


(**
   This modules performs some additonal analysis on the result
   of Findloops and returns a sorted list of loops. The loops should
   then be parallelized in the order of the output list.
*)


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
    it is a simpler task (we order loops by their 'compleixity')
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

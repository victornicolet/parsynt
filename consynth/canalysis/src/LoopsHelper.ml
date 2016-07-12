open Cil
open Utils
open ListTools

let removeFromCFG (stm : stmt) =
  let succs = stm.succs in
  let preds = stm.preds in
  let eq_stm s = (stm.sid = s.sid) in
  List.iter (fun s -> (s.succs <- List.filter eq_stm s.succs)) preds;
  List.iter (fun s -> (s.preds <- List.filter eq_stm s.preds)) succs

let rec remLastInstr (bdy : stmt list) =
  if List.length bdy < 1
  then None, None
  else
    let lastStmt = last bdy in
    match lastStmt.skind with
    | Instr il ->
       begin
         match il with
         | [i] ->
            begin
              removeFromCFG lastStmt;
              let stmtli = (remove_last bdy) in
              Some i, Some stmtli
            end

         | hd::tl ->
            begin
              lastStmt.skind <- Instr (remove_last il);
              Some (last il), Some bdy
            end

         | [] -> None, None
       end

    | Block b -> remLastInstr b.bstmts

    | _ -> None, Some bdy

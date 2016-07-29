open Utils
open Cil
open List


let (v) = VS.union

let rec read (b : block) =
  fold_left
    (fun vs stmt ->
      (read_stmt stmt) v vs)
    VS.empty
    b.bstmts


and read_stmt (stmt : stmt) =
  match stmt.skind with
  | Instr il ->
      fold_left (fun vs instr ->  (read_instr instr) v vs) VS.empty il

  | Return (eo, loc) ->
     appOptionDefault read_expr eo VS.empty

  | If (c, bi , be, _) ->
     VSOps.unions [(read_expr c); (read bi); (read be)]

  | Loop (b, _, _, _) -> read b

  | Switch (e, b, sl, _) ->
     VSOps.unions ([read_expr e; read b]@(map read_stmt sl))

  | Block b -> read b

  | TryFinally (b1, b2, _) -> VS.union (read b1) (read b2)

  | TryExcept (b1, (il, e) , b2, _) ->
     VSOps.unions
       ([read b1; read b2; read_expr e]@(map read_instr il))

  | _ -> VS.empty


and read_instr (instr : instr) =
  match instr with
  | Set (lv, e, _) ->
     VS.union (index l)

and read_expr (expr : exp) = VS.empty

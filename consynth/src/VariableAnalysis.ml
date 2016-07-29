open Utils
open Cil
open List
open VSOps

let un = VS.union
let empty = VS.empty
let uns = VSOps.unions

(** Read set of a block/stmt/instr/expression *)

let rec read (b : block) =
  union_map b.bstmts read_stmt


and read_stmt (stmt : stmt) =
  match stmt.skind with
  | Instr il ->
      union_map il read_instr

  | Return (eo, loc) ->
     appOptionDefault read_expr eo empty

  | If (c, bi , be, _) ->
     uns [(read_expr c); (read bi); (read be)]

  | Loop (b, _, _, _) -> read b

  | Switch (e, b, sl, _) ->
     uns ([read_expr e]@(map read_stmt sl))

  | Block b -> read b

  | TryFinally (b1, b2, _) -> un (read b1) (read b2)

  | TryExcept (b1, (il, e) , b2, _) ->
     uns ([read b1; read b2; read_expr e]@(map read_instr il))

  | _ -> empty


and read_instr (instr : instr) =
  match instr with
  | Set (lv, e, _) ->
     un (index lv) (read_expr e)

  | Call (lvo, ef,  args, _) ->
     un
       (appOptionDefault index lvo empty)
       (uns (map read_expr args))

  | _ -> empty


and read_expr (expr : exp) =
  match expr with
  | Lval lv | AddrOf lv | StartOf lv -> un (index lv) (basic lv)
  | UnOp (_, e, _) | CastE (_, e) -> read_expr e
  | BinOp (_, e, e', _) -> un (read_expr e) (read_expr e')
  | _ -> empty

and basic ((host, offset) : lval) =
  match host with
  | Var v -> VS.singleton v
  | _ -> empty

(** Retrieve indexes *)

and index ((host, offset) : lval) =
  let vs =
    match host with
    | Mem e -> read_expr e
    | _ -> VS.empty
  in un vs (index_o offset)

and index_o =
  function
  | NoOffset -> empty
  | Field (fi, o) -> index_o o
  | Index (e, o) -> un (read_expr e) (index_o o)


(** Write set *)
let rec write (b : block) =
  union_map b.bstmts write_stmt

and write_stmt (stm : stmt) =
  match stm.skind with
  | Instr il -> union_map il write_instr
  | If (c, bi, be, _) -> un (write bi) (write be)
  | Loop (b, _, _, _) -> write b
  | Switch (_, _, sl, _) -> union_map sl write_stmt
  | Block b -> write b
  | _ -> empty

and write_instr (inst : instr) =
  match inst with
  | Set (lv, e, _) -> basic lv
  | Call (lvo, _, _, _) -> appOptionDefault basic lvo empty
  | _ -> empty

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
     maybe_apply_default read_expr eo empty

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
       (maybe_apply_default index lvo empty)
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
  | Call (lvo, _, _, _) -> maybe_apply_default basic lvo empty
  | _ -> empty


let used b = un (write b) (read b)

let rec aliased b =
  union_map b.bstmts aliased_stmt

and aliased_stmt stmt =
  match stmt.skind with
  | Instr il -> union_map il aliased_instr
  | Block b -> aliased b
  | Return (eo, _) -> maybe_apply_default aliased_expr eo empty
  | If(c, b1, b2, _) -> un (un (aliased_expr c) (aliased b1)) (aliased b2)
  | Loop(b, _, _, _) -> aliased b
  | Switch (e, _ , sl, _) ->
     un (aliased_expr e) (union_map sl aliased_stmt)
  | _ -> empty

and aliased_instr instr =
  match instr with
  | Set (lv, e, _) -> un (aliased_expr e) (aliased_lval lv)
  | Call (lvo, ef, args, _) ->
     un (maybe_apply_default aliased_lval lvo empty) (union_map args aliased_expr)
  | _ -> empty

and aliased_expr expr =
  match expr with
  | Lval lv -> aliased_lval lv
  | StartOf lv| AddrOf lv -> un (basic lv) (aliased_lval lv)
  | UnOp(_ ,e, _)  | CastE (_, e) -> aliased_expr e
  | BinOp (_, e, e', _) -> un (aliased_expr e) (aliased_expr e')
  | _ -> empty

and aliased_lval (host, offset) =
  match host with
  | Var v -> aliased_o offset
  | Mem e -> un (aliased_o offset) (aliased_expr e)

and aliased_o off =
  match off with
  | NoOffset -> empty
  | Field (f, o) -> aliased_o o
  | Index (e, o) -> un (aliased_o o) (aliased_expr e)

(** Variable classification *)
let is_simple v =
  match v.vtype with
  | TFloat _ | TInt _ | TEnum _ -> true
  | _ -> false

let is_complex v =
  match v.vtype with
  | TComp _ -> true | _ -> false

let is_array v =
  match v.vtype with
  | TArray _ -> true | _ -> false

let is_pointer v =
  match v.vtype with
  | TPtr  _ -> true | _ -> false

(** Set of analyzable variables of b *)
let analyzable b =
  let simple_vars = VS.filter is_simple (used b) in
  let complex_vars = VS.filter is_complex (used b) in
  VS.diff (un simple_vars complex_vars) (aliased b)


(** Host / Offset *)
let rec analyze_host host  =
  match host with
  | Var vi -> [vi], []
  | Mem e ->
     match e with
     | Lval (host, offset) ->
        let o2 = analyze_offset offset in
        let v, o1 = analyze_host host in
        v, o1@o2
     | Binop (op, (Lval (host, offset), e2, t)) ->
        match op with
        (** PlusPI and IndexPI are semantically equivalent *)
        | PlusPI
        | IndexPI ->
        | MinusPI ->
        | _ -> failwith "Unexpected operator in Lval host expressions"

and analyze_offset offset =

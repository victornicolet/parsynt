open Utils
open Cil
open List
open VSOps

let un = VS.union
let empty = VS.empty
let uns = VSOps.unions

(** Read set of a block/stmt/instr/expression *)

let rec va_read (b : block) =
  union_map b.bstmts va_read_stmt


and va_read_stmt (stmt : stmt) =
  match stmt.skind with
  | Instr il ->
      union_map il va_read_instr

  | Return (eo, loc) ->
     maybe_apply_default va_read_expr eo empty

  | If (c, bi , be, _) ->
     uns [(va_read_expr c); (va_read bi); (va_read be)]

  | Loop (b, _, _, _) -> va_read b

  | Switch (e, b, sl, _) ->
     uns ([va_read_expr e]@(map va_read_stmt sl))

  | Block b -> va_read b

  | TryFinally (b1, b2, _) -> un (va_read b1) (va_read b2)

  | TryExcept (b1, (il, e) , b2, _) ->
     uns ([va_read b1; va_read b2; va_read_expr e]@(map va_read_instr il))

  | _ -> empty


and va_read_instr (instr : instr) =
  match instr with
  | Set (lv, e, _) ->
     un (index lv) (va_read_expr e)

  | Call (lvo, ef,  args, _) ->
     un
       (maybe_apply_default index lvo empty)
       (uns (map va_read_expr args))

  | _ -> empty


and va_read_expr (expr : exp) =
  match expr with
  | Lval lv | AddrOf lv | StartOf lv -> un (index lv) (basic lv)
  | UnOp (_, e, _) | CastE (_, e) -> va_read_expr e
  | BinOp (_, e, e', _) -> un (va_read_expr e) (va_read_expr e')
  | _ -> empty

and basic ((host, offset) : lval) =
  match host with
  | Var v -> VS.singleton v
  | _ -> empty

(** Retrieve indexes *)

and index ((host, offset) : lval) =
  let vs =
    match host with
    | Mem e -> va_read_expr e
    | _ -> VS.empty
  in un vs (index_o offset)

and index_o =
  function
  | NoOffset -> empty
  | Field (fi, o) -> index_o o
  | Index (e, o) -> un (va_read_expr e) (index_o o)


(** Va_Write set *)
let rec va_write (b : block) =
  union_map b.bstmts va_write_stmt

and va_write_stmt (stm : stmt) =
  match stm.skind with
  | Instr il -> union_map il va_write_instr
  | If (c, bi, be, _) -> un (va_write bi) (va_write be)
  | Loop (b, _, _, _) -> va_write b
  | Switch (_, _, sl, _) -> union_map sl va_write_stmt
  | Block b -> va_write b
  | _ -> empty

and va_write_instr (inst : instr) =
  match inst with
  | Set (lv, e, _) -> basic lv
  | Call (lvo, _, _, _) -> maybe_apply_default basic lvo empty
  | _ -> empty


let used b = un (va_write b) (va_read b)

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
    un (maybe_apply_default aliased_lval lvo empty)
      (union_map args aliased_expr)
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
  | Var vi -> Some vi, []
  | Mem e ->
     match e with
     | Lval (host, offset) ->
        let o2 = analyze_offset offset in
        let v, o1 = analyze_host host in
        v, o1@o2
     | BinOp (op, Lval (host, offset), e2, t) ->
        let host_varinfo_opt =
          match analyze_host host with
          | Some vinf , [] -> Some vinf
          | _, _ -> None
        in
        let expr_op =
          match op with
          (** PlusPI and IndexPI are semantically equivalent *)
          | PlusPI
          | IndexPI ->
             e2
          | MinusPI ->
             UnOp (Neg, e2, t)
          | _ -> failwith "Unexpected operator in Lval host expressions"
        in
        host_varinfo_opt, [expr_op]

     |_ -> None, []

and analyze_offset offset =
  match offset with
  | NoOffset -> []
  | Index (e, off) -> e :: (analyze_offset off)
  | _ -> []

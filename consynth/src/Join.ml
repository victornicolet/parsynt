open SketchTypes
open Utils
open SPretty


(**

*)

let rec make_holes (state : VS.t) =
  function
  | SkVar sklv ->
     begin
       match vi_of sklv with
       | None -> failwith "State expression should not appear here"
       | Some vi ->
          let t = symb_type_of_ciltyp vi.Cil.vtype in
          if VS.mem vi state
          then SkHoleL (sklv, t)
          else SkHoleR t
     end

  | SkConst c -> SkHoleR Unit

  | SkFun skl -> SkFun (make_join state skl)

  | SkBinop (op, e1, e2) ->
     let holes1 = make_holes state e1 in
     let holes2 = make_holes state e2 in
     merge_holes holes1 holes2 (fun a b -> SkBinop(op, a, b))

  | SkUnop (op, e) ->
     SkUnop(op, make_holes state e)

  | SkCond (c, li, le) ->
     SkCond (make_holes state c, make_join state li, make_join state le)

  | SkQuestion (c, ei, ee) ->
     let h1 = make_holes state ei in
     let h2 = make_holes state ee in
     let hc = make_holes state c in
     merge_holes h1 h2 (fun a b -> SkQuestion (hc, a, b))

  | _ as skexpr ->  skexpr


and merge_holes h1 h2 f =
  if h1 = h2 then h1 else f h1 h2

and make_join state =
  function
  | SkLetExpr li ->
     SkLetExpr (List.map (fun (v, e) -> (v, make_holes state e)) li)
  | SkLetIn (li, cont) ->
     SkLetIn ((List.map (fun (v, e) -> (v, make_holes state e)) li),
              make_join state cont)

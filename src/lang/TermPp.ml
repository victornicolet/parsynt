open Base
open Fmt
open Term
open Typ
open Utils

(* ============================================================================================= *)
(*  PRETTY PRINTING *)
(* ============================================================================================= *)

let rec pp_binop (formt : Formatter.t) (b : Binop.t) =
  if Fmt.utf_8 formt then
    match b with
    | Times -> Fmt.string formt "*"
    | Div -> Fmt.string formt "/"
    | Mod -> Fmt.string formt "%"
    | Plus -> Fmt.string formt "+"
    | Minus -> Fmt.string formt "-"
    | Max -> Fmt.string formt "max"
    | Min -> Fmt.string formt "min"
    | And -> Fmt.string formt "&&"
    | Or -> Fmt.string formt "||"
    | Xor -> Fmt.string formt "xor"
    | Impl -> Fmt.string formt "=>"
    | Concat -> Fmt.string formt "++"
    | Cons -> Fmt.string formt "."
    | Lt -> Fmt.string formt "<"
    | Gt -> Fmt.string formt ">"
    | Le -> Fmt.string formt "<="
    | Ge -> Fmt.string formt ">="
    | Eq -> Fmt.string formt "="
    | At -> Fmt.string formt "@"
    | BChoice c -> Fmt.(pf formt "@[(choose %a)@]" (list ~sep:sp pp_binop) c)
  else
    match b with
    | Times -> Fmt.string formt "*"
    | Div -> Fmt.string formt "/"
    | Mod -> Fmt.string formt "%"
    | Plus -> Fmt.string formt "+"
    | Minus -> Fmt.string formt "-"
    | Max -> Fmt.string formt "max"
    | Min -> Fmt.string formt "min"
    | And -> Fmt.string formt "&&"
    | Or -> Fmt.string formt "||"
    | Xor -> Fmt.string formt "xor"
    | Impl -> Fmt.string formt "=>"
    | Concat -> Fmt.string formt "++"
    | Cons -> Fmt.string formt "."
    | Lt -> Fmt.string formt "<"
    | Gt -> Fmt.string formt ">"
    | Le -> Fmt.string formt "<="
    | Ge -> Fmt.string formt ">="
    | Eq -> Fmt.string formt "="
    | At -> Fmt.string formt "@"
    | BChoice c -> Fmt.(pf formt "@[(choose %a)@]" (list ~sep:sp pp_binop) c)

let rec pp_unop (formt : Formatter.t) (u : Unop.t) =
  if Fmt.utf_8 formt then
    match u with
    | Id -> Fmt.string formt "ⅈ"
    | Neg -> Fmt.string formt "-"
    | Not -> Fmt.string formt "¬"
    | Hd -> Fmt.string formt "hd"
    | Tl -> Fmt.string formt "tl"
    | Abs -> Fmt.string formt "abs"
    | IsEmpty -> Fmt.string formt "empty?"
    | Take _ -> Fmt.string formt "take"
    | UChoice c -> Fmt.(pf formt "@[(choose %a)@]" (list ~sep:sp pp_unop) c)
  else
    match u with
    | Id -> Fmt.string formt "id"
    | Neg -> Fmt.string formt "-"
    | Not -> Fmt.string formt "not"
    | Hd -> Fmt.string formt "hd"
    | Tl -> Fmt.string formt "tl"
    | Abs -> Fmt.string formt "abs"
    | Take _ -> Fmt.string formt "take"
    | IsEmpty -> Fmt.string formt "empty?"
    | UChoice c -> Fmt.(pf formt "@[(choose %a)@]" (list ~sep:sp pp_unop) c)

let sep_and formt () = if utf_8 formt then pf formt "@;∧@;" else pf formt "@;&&@;"

let pp_lhvar formt lhv =
  let unstyled formt lhv = match lhv with Var v -> pp_variable formt v in
  styled `Cyan unstyled formt lhv

let pp_lhvar_t (formt : Formatter.t) (lhv : lhvar) =
  match lhv with Var v -> Fmt.(pair ~sep:colon pp_variable pp_typ formt (v, v.vtype))

let pp_constant (formt : Formatter.t) (cst : Constant.t) =
  match cst with
  | CInt i -> Fmt.(int formt i)
  | CBool b -> Fmt.(bool formt b)
  | CEmpty -> Fmt.(brackets nop formt ())
  | CNone -> Fmt.(pf formt "(*)")

let rec pp_term_r usep (formt : Formatter.t) (t : term) =
  let _parens = if usep then Fmt.parens else identity in
  match t.texpr with
  | EEmpty -> Fmt.(box string formt "(empty)")
  | EBin (b, e1, e2) -> (
      let _parens = match b with Or -> identity | _ -> _parens in
      match b with
      | At ->
          Fmt.(
            box ~indent:2
              (_parens (fun f () -> pf f "%a[%a]" (pp_term_r true) e1 (pp_term_r true) e2))
              formt ())
      | Min | Max ->
          Fmt.(
            box ~indent:2
              (_parens (fun f () ->
                   pf f "%a@;(%a,@;%a)"
                     (styled (`Fg `Yellow) pp_binop)
                     b (pp_term_r true) e1 (pp_term_r true) e2))
              formt ())
      | _ ->
          Fmt.(
            box ~indent:2
              (_parens (fun f () ->
                   pf f "%a@;%a@;%a" (pp_term_r true) e1
                     (styled (`Fg `Yellow) pp_binop)
                     b (pp_term_r true) e2))
              formt ()) )
  | EConst c -> pp_constant formt c
  | EIte (c, e1, e2) ->
      Fmt.(
        box ~indent:2
          (_parens (fun f () ->
               pf f "%a@;%a@;%a@;%a@;%a@;%a"
                 (styled (`Fg `Yellow) string)
                 "if" (pp_term_r false) c
                 (styled (`Fg `Yellow) string)
                 "then" (pp_term_r false) e1
                 (styled (`Fg `Yellow) string)
                 "else" (pp_term_r false) e2))
          formt ())
  | ESetL (a, i, e) ->
      Fmt.(
        box ~indent:2
          (_parens (fun f () ->
               pf f "set@;%a@;@;%a@;%a" (pp_term_r true) a (pp_term_r true) i (pp_term_r true) e))
          formt ())
  | EWith (s, n, b) ->
      Fmt.(
        box ~indent:2
          (_parens (fun f () ->
               pf f "%a@;with@;%s@;=@;%a" (box (pp_term_r true)) s n (box (pp_term_r false)) b))
          formt ())
  | EUn (u, e) -> (
      match u with
      | Take i -> Fmt.(pf formt "%a[%a:]" (pp_term_r true) e (pp_term_r false) i)
      | _ -> Fmt.(box ~indent:2 (_parens (pair ~sep:sp pp_unop (pp_term_r true))) formt (u, e)) )
  | EVar lhv ->
      if has_attr (Offset (-1)) t then Fmt.(fun f lhv -> pf f "%a#" pp_lhvar lhv) formt lhv
      else pp_lhvar formt lhv
  | EHole _ -> Fmt.string formt "(??)"
  | ETuple el -> Fmt.(box (parens (list ~sep:comma (pp_term_r false))) formt el)
  | EList el -> Fmt.(box (brackets (list ~sep:semicolon (pp_term_r false))) formt el)
  | EChoice el -> Fmt.(pf formt "<%a>" (box (list ~sep:colon (pp_term_r false))) el)
  | EMem (e, i) -> Fmt.(box (pair ~sep:nop (pp_term_r true) (parens int)) formt (e, i))
  | EMemStruct (_, n, e) -> Fmt.(pf formt "%a.%s" (pp_term_r true) e n)
  | EStruct mems ->
      Fmt.(
        box
          (braces
             (list
                ~sep:(fun fmt () -> pf fmt ";@;")
                (box (pair ~sep:(fun fmt () -> pf fmt " = ") string (pp_term_r false)))))
          formt mems)
  | ELambda (vl, e) ->
      Fmt.(
        box ~indent:2
          (_parens (fun f () ->
               pf f "fun @[%a@] ->@;%a"
                 (_parens (list ~sep:sp pp_variable))
                 vl
                 (box (pp_term_r false))
                 e))
          formt ())
  | EFoldL (f, ei, le) ->
      Fmt.(
        pf formt "@[%a@;@[<hov 2>~f:%a@;~init:(%a)@;%a@]@]"
          (styled (`Fg `Red) string)
          "List.fold"
          (box (pp_term_r true))
          f
          (box (pp_term_r false))
          ei
          (box (pp_term_r true))
          le)
  | EFoldR (f, ei, le) ->
      Fmt.(
        pf formt "@[%a@;@[<hov 2>%a@;%a@;%a@]@]"
          (styled (`Fg `Red) string)
          "foldr"
          (box (pp_term_r true))
          f
          (box (pp_term_r true))
          ei
          (box (pp_term_r true))
          le)
  | EApp (f, el) ->
      Fmt.(
        box ~indent:2
          (_parens (pair ~sep:sp (pp_term_r true) (list ~sep:sp (pp_term_r true))))
          formt (f, el))
  | ELet (Var v, e, e') ->
      Fmt.(
        pf formt "@[<hov 2>@[<hov 2>%a %a =@;%a@]@;%a@;%a@]"
          (styled `Bold string)
          "let" pp_variable v
          (box (pp_term_r true))
          e
          (styled `Bold string)
          "in"
          (box (pp_term_r false))
          e')
  | ELetValues (v, e, e') ->
      Fmt.(
        pf formt "@[<v 2>@[%a %a =@]@;%a@;%a@;%a@]"
          (styled `Bold string)
          "let" (list ~sep:comma pp_variable) v
          (box (pp_term_r true))
          e
          (styled `Bold string)
          "in"
          (box (pp_term_r true))
          e')
  | EPLet (bindings, e) ->
      let pp_bindings =
        Fmt.(
          box
            (list
               ~sep:(fun f () -> pf f "and")
               (pair ~sep:(fun f () -> pf f "@;=@;") pp_lhvar_t (pp_term_r true))))
      in
      Fmt.(
        box ~indent:2
          (pair ~sep:sp
             (pair ~sep:sp (pair ~sep:sp (styled `Bold string) pp_bindings) (styled `Bold string))
             (box (pp_term_r true)))
          formt
          ((("let", bindings), "in"), e))

let pp_term = pp_term_r false

let pp_term_list (formt : Formatter.t) (el : term list) = Fmt.(box (list (pp_term_r true)) formt el)

(* ============================================================================================= *)
(*  PRETTY PRINTING - ROSETTE FORMAT *)
(* ============================================================================================= *)

let rec rpp_binop (formt : Formatter.t) (b : Binop.t) =
  match b with
  | Times -> Fmt.string formt "*"
  | Div -> Fmt.string formt "/"
  | Mod -> Fmt.string formt "modulo"
  | Plus -> Fmt.string formt "+"
  | Minus -> Fmt.string formt "-"
  | Max -> Fmt.string formt "max"
  | Min -> Fmt.string formt "min"
  | And -> Fmt.string formt "&&"
  | Or -> Fmt.string formt "||"
  | Xor -> Fmt.string formt "xor"
  | Impl -> Fmt.string formt "implies"
  | Concat -> Fmt.string formt "append"
  | Cons -> Fmt.string formt "."
  | Lt -> Fmt.string formt "<"
  | Gt -> Fmt.string formt ">"
  | Le -> Fmt.string formt "<="
  | Ge -> Fmt.string formt ">="
  | Eq -> Fmt.string formt "="
  | At -> Fmt.string formt "list-ref"
  | BChoice c -> Fmt.(pf formt "@[(choose %a)@]" (list ~sep:sp rpp_binop) c)

and rpp_unop (formt : Formatter.t) (u : Unop.t) =
  match u with
  | Id -> Fmt.string formt "identity"
  | Neg -> Fmt.string formt "-"
  | Not -> Fmt.string formt "not"
  | Hd -> Fmt.string formt "car"
  | Tl -> Fmt.string formt "rest"
  | Abs -> Fmt.string formt "abs"
  | IsEmpty -> Fmt.string formt "empty?"
  | Take e -> Fmt.(pf formt "(lambda ($$x) (take $$x %a))" rpp_term_r e)
  | UChoice c -> Fmt.(pf formt "@[(choose %a)@]" (list ~sep:sp rpp_unop) c)

and rpp_lhvar formt lhv =
  match lhv with
  | Var v ->
      if Variable.(v = _INT_MAX) then Fmt.int formt int_range
      else if Variable.(v = _INT_MIN) then Fmt.int formt (-int_range)
      else pp_variable formt v

and rpp_constant (formt : Formatter.t) (cst : Constant.t) =
  match cst with
  | CInt i -> Fmt.(int formt i)
  | CBool b -> if b then Fmt.(pf formt "#t") else Fmt.(pf formt "#f")
  | CEmpty -> Fmt.(brackets nop formt ())
  | CNone -> Fmt.(pf formt "(??)")

and rpp_term_r (formt : Formatter.t) (t : term) =
  match t.texpr with
  | EEmpty -> Fmt.((styled `Bold (box string)) formt "(empty)")
  | EBin (b, e1, e2) ->
      Fmt.(
        box ~indent:2
          (parens (fun f () ->
               pf f "%a@;%a@;%a" (styled (`Fg `Yellow) rpp_binop) b rpp_term_r e1 rpp_term_r e2))
          formt ())
  | EConst c -> rpp_constant formt c
  | EIte (c, e1, e2) ->
      Fmt.(
        box ~indent:2
          (parens (fun f () ->
               pf f "%a@;%a@;%a@;%a"
                 (styled (`Fg `Yellow) string)
                 "if" rpp_term_r c rpp_term_r e1 rpp_term_r e2))
          formt ())
  | ESetL (a, i, e) ->
      Fmt.(
        box ~indent:2
          (parens (fun f () -> pf f "list-set@;%a@;@;%a@;%a" rpp_term_r a rpp_term_r i rpp_term_r e))
          formt ())
  | EWith (_, _, _) -> failwith "Unsupported, wtf racket."
  | EUn (u, e) -> (
      match u with
      | Take i -> Fmt.(pf formt "@[(take@;%a@;%a)@]" rpp_term_r e rpp_term_r i)
      | _ -> Fmt.(box ~indent:2 (parens (pair ~sep:sp rpp_unop rpp_term_r)) formt (u, e)) )
  | EVar lhv ->
      if has_attr (Offset (-1)) t then Fmt.(fun f lhv -> pf f "%a#" rpp_lhvar lhv) formt lhv
      else rpp_lhvar formt lhv
  | EHole _ -> Fmt.(styled (`Fg `Blue) string) formt "(??)"
  | ETuple el ->
      Fmt.(box (parens (fun f () -> pf f "values %a" (list ~sep:sp rpp_term_r) el)) formt ())
  | EList el ->
      if List.length el > 0 then
        Fmt.(box (parens (fun f () -> pf f "list %a" (list ~sep:sp rpp_term_r) el)) formt ())
      else Fmt.(pf formt "(list)")
  | EChoice el ->
      if List.length el > 0 then
        Fmt.(box (parens (fun f () -> pf f "choose @[%a@]" (list ~sep:sp rpp_term_r) el)) formt ())
      else Fmt.(pf formt "(??)")
  | EMem (e, i) -> Fmt.(box (parens (fun f () -> pf f "list-ref@;%a@;%i" rpp_term_r e i)) formt ())
  | EMemStruct (s, n, e) ->
      Fmt.(box (parens (fun f () -> pf f "%s-%s@;%a" s n rpp_term_r e)) formt ())
  | EStruct fields -> (
      match type_of t with
      | Ok (TStruct (s, _)) ->
          Fmt.(
            box
              (parens (fun f () ->
                   pf f "%s@;%a" s (list ~sep:sp rpp_term_r) (Utils.ListTools.lsnd fields)))
              formt ())
      | Ok t ->
          Log.error (fun f () ->
              Fmt.(
                pf f "Failed to print struct with fields %a."
                  (list ~sep:sp (pair ~sep:colon string rpp_term_r))
                  fields));
          Log.error (printer_msg "Got type %a." pp_typ t);
          Structs.dump_state ();
          failwith "Cannot print struct"
      | Error (s, t, e) ->
          Log.error (fun frmt () ->
              Fmt.(
                pf frmt "@[Typechecking:@;message : %s@;type : %a@;expr : %a@]@." s pp_typ t
                  rpp_term_r (mk_term e)));
          Log.error (fun f () ->
              Fmt.(
                pf f "Failed to find struct with fields %a."
                  (list ~sep:sp (pair ~sep:colon string rpp_term_r))
                  fields));
          Structs.dump_state ();
          failwith "Cannot print struct" )
  | ELambda (vl, e) ->
      Fmt.(
        box ~indent:2
          (parens (fun f () ->
               pf f "lambda@;%a@;%a" (parens (list ~sep:sp pp_variable)) vl rpp_term_r e))
          formt ())
  | EFoldL (f, ei, le) ->
      Fmt.(pf formt "@[(foldl@;%a@;%a@;%a)@]" rpp_term_r f rpp_term_r ei rpp_term_r le)
  | EFoldR (f, ei, le) ->
      Fmt.(
        box ~indent:2 (parens (pair string (list ~sep:sp rpp_term_r))) formt ("foldr", [ f; ei; le ]))
  | EApp (f, el) ->
      Fmt.(box ~indent:2 (parens (pair ~sep:sp rpp_term_r (list ~sep:sp rpp_term_r))) formt (f, el))
  | ELet (v, e, e') ->
      Fmt.(
        box ~indent:2
          (parens (fun f () -> pf f "let@;([%a@;%a])@;%a" rpp_lhvar v rpp_term_r e rpp_term_r e'))
          formt ())
  | ELetValues (v, e, e') ->
      Fmt.(
        box ~indent:2
          (parens (fun f () ->
               pf f "let-values@;([(%a)@;%a])@;%a" (list ~sep:sp string)
                 (List.map ~f:(fun v -> v.vname) v)
                 rpp_term_r e rpp_term_r e'))
          formt ())
  | EPLet (bindings, e) ->
      let rpp_bindings frmt bd =
        Fmt.(box (list ~sep:sp (brackets (pair ~sep:sp rpp_lhvar rpp_term_r))) frmt bd)
      in
      Fmt.(
        box ~indent:2
          (parens (fun f () -> pf f "let@;(%a)@;%a" rpp_bindings bindings rpp_term_r e))
          formt ())

let rpp_term = rpp_term_r

let rpp_term_list (formt : Formatter.t) (el : term list) = Fmt.(box (list rpp_term_r) formt el)

let typecheck_err ((s, t, e) : string * typ * expr) =
  Log.error (fun frmt () ->
      Fmt.(
        pf frmt "@[Typechecking:@;message : %s@;type : %a@;expr : %a@]@." s pp_typ t rpp_term
          (mk_term e)))

let type_term_exn t =
  match type_term t with
  | Ok t -> t
  | Error e ->
      typecheck_err e;
      failwith "type_term_exn"

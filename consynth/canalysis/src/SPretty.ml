open Cil
open Utils
open PpHelper
open SketchTypes
open Format
open Loops

(** Basic pretty-printing *)
let rec pp_skstmt ppf ((vi, sklet) : varinfo * sklet)  =
  Format.fprintf  ppf "%s = %sbegin%s@.@[%a@] %send%s\n"
    vi.vname
    (color "yellow") default
    pp_sklet sklet
    (color "yellow") default

and pp_sklet ppf =
  function
  | SkLetExpr e -> pp_skexpr ppf e
  | SkLetIn (vi, e, l) ->
     Format.fprintf ppf "@[%slet%s %s = %a %sin%s@] %a"
       (color "red") default
       vi.vname pp_skexpr e
       (color "red") default
       pp_sklet l

and pp_skexpr (ppf : Format.formatter) skexpr =
let fp = Format.fprintf in
  match skexpr with
  | SkVar i -> fp ppf "%s" i.vname
  | SkConst c -> fp ppf "const %s" (psprint80 Cil.d_const c)
  | SkLval l -> fp ppf "%s" (psprint80 Cil.d_lval l)
  | SkHoleR -> fp ppf "(??_R)"
  | SkHoleL -> fp ppf "(??_L)"
  | SkAddrof e -> fp ppf "(AddrOf )"
  | SkAddrofLabel addr -> fp ppf "(AddrOfLabel)"
  | SkAlignof typ -> fp ppf "(AlignOf typ)"
  | SkAlignofE e -> fp ppf "(AlignOfE %a)" pp_skexpr e
  | SkArray (v, subsd) ->
     fp ppf "%s[%a]" v.vname (fun fmt -> ppli fmt pp_skexpr) subsd
  | SkCil e -> fp ppf "<cil expr>"
  | SkBinop (op, e1, e2) ->
     fp ppf "%a %s %a"
       pp_skexpr e1 (psprint80 Cil.d_binop op) pp_skexpr e2
  | SkUnop (op, e) ->
     fp ppf "%s %a" (psprint80 Cil.d_unop op) pp_skexpr e
  | SkCond (c, e1, e2) ->
      fp ppf "%sif%s @[%a@] then @[%a@] else @[%a@]"
        (color "blue") default
       pp_skexpr c pp_skexpr e1 pp_skexpr e2
  | SkRec ((i, g, u), e) ->
     fp ppf "%s recursive(%s %s;%s) %s %a"
       (color "blue")
       (psprint80 Cil.dn_instr i)
       (psprint80 Cil.dn_exp g)
       (psprint80 Cil.dn_instr u)
       default
       pp_skexpr e
  | SkSizeof t -> fp ppf "(SizeOf %s)" (psprint80 Cil.d_type t)
  | SkSizeofE e -> fp ppf "(SizeOf %a)" pp_skexpr e
  | SkSizeofStr str -> fp ppf "(SizeOf %s)" str
  | SkCastE (t,e) ->
     fp ppf "(%s) %a" (psprint80 Cil.d_type t) pp_skexpr e
  | SkStartOf l -> fp ppf "(StartOf %s)" (psprint80 Cil.d_lval l)



let printSkstmt s = pp_skstmt Format.std_formatter s
let sprintSkstmt s =
  pp_skstmt Format.str_formatter s;
  Format.flush_str_formatter ()

let eprintSkstmt s = pp_skstmt Format.err_formatter s

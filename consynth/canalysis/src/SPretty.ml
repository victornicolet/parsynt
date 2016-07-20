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
  | SkLetExpr el ->
     pp_print_list (fun ppf (v,e) -> pp_skexpr ppf e) ppf el

  | SkLetIn (el, l) ->
     fprintf ppf "@[(%slet%s (%a)@;%a@]"
       (color "red") default
       (fun ppf el ->
         (pp_print_list
            (fun ppf (v, e) ->
              Format.fprintf ppf "@[ [%a %a]"
                pp_sklvar v pp_skexpr e) ppf el)) el
       pp_sklet l

and pp_sklvar (ppf : Format.formatter) sklvar =
  match sklvar with
  | SkState -> fprintf ppf "<s>"
  | SkVarinfo v -> fprintf ppf "%s" v.Cil.vname

and pp_skexpr (ppf : Format.formatter) skexpr =
let fp = Format.fprintf in
  match skexpr with
  | SkVar i -> fp ppf "%s" i.vname
  | SkConst c -> fp ppf "const %s" (psprint80 Cil.d_const c)
  | SkFun l -> pp_sklet ppf l
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
       pp_skexpr c pp_sklet e1 pp_sklet e2
  | SkQuestion (c, e1, e2) ->
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
       pp_sklet e
  | SkSizeof t -> fp ppf "(SizeOf %s)" (psprint80 Cil.d_type t)
  | SkSizeofE e -> fp ppf "(SizeOf %a)" pp_skexpr e
  | SkSizeofStr str -> fp ppf "(SizeOf %s)" str
  | SkCastE (t,e) ->
     fp ppf "(%s) %a" (psprint80 Cil.d_type t) pp_skexpr e
  | SkStartOf l -> fp ppf "(StartOf %s)" (psprint80 Cil.d_lval l)


(** Print statements **)
let printSkstmt s = pp_skstmt std_formatter s
let sprintSkstmt s =
  pp_skstmt str_formatter s;
  flush_str_formatter ()

let eprintSkstmt s = pp_skstmt err_formatter s

(** Print let-forms *)
let printSklet s = pp_sklet std_formatter s
let sprintSklet s =
  pp_sklet str_formatter s;
  flush_str_formatter ()

let eprintSklet s = pp_sklet err_formatter s

(** Print epxressions *)
let printSkexpr s = pp_skexpr std_formatter s
let sprintSkexpr s =
  pp_skexpr str_formatter s;
  flush_str_formatter ()

let eprintSkexpr s = pp_skexpr err_formatter s

(** Pritn the whole intermediary sketch *)
let pp_sketch ppf (state_set, stmt_li) =
  fprintf ppf "@[State = %a@]@;@[%a@]"
    VSOps.pvs state_set
    (pp_print_list
       ~pp_sep:(fun fmt x -> fprintf fmt "\n@.")
       pp_skstmt) stmt_li

(** Print sketches *)
let printSketch s = pp_sketch std_formatter s
let sprintSketch s =
  pp_sketch str_formatter s;
  flush_str_formatter ()

let eprintSketch s = pp_sketch err_formatter s

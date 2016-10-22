open SketchTypes
open Format
open Utils

module Ct = Utils.CilTools
module VS = Utils.VS

(** String representing holes *)
let ch_l_nums = ref ""
let ch_l_bools = ref ""
let ch_r_nums = ref ""
let ch_r_bools = ref ""

let current_expr_depth = ref 1
let state_struct_name = ref "__state"

let state_vars = ref VS.empty

(**
   TODO : find a way to be able to generate different hole
   expressions for R-holes and L-holes. Also, might be useful
   to refine available variables with the type of the hole.
*)
let ref_concat l = List.fold_left (fun ls s-> ls^" "^(!s)) "" l

let set_hole_vars lvs rvs =
  let left_hole_nums, left_hole_bools, right_hole_nums, right_hole_bools =
    VS.filter (fun vi ->
        Ct.is_of_real_type vi.Cil.vtype || Ct.is_of_int_type vi.Cil.vtype) lvs,
    VS.filter (fun vi -> Ct.is_of_bool_type vi.Cil.vtype) lvs,
    VS.filter (fun vi ->
        Ct.is_of_real_type vi.Cil.vtype || Ct.is_of_int_type vi.Cil.vtype) rvs,
    VS.filter (fun vi -> Ct.is_of_bool_type vi.Cil.vtype) rvs
  in
    ch_l_nums := VSOps.to_string left_hole_nums;
    ch_l_bools := VSOps.to_string left_hole_bools;
    ch_r_nums := VSOps.to_string right_hole_nums;
    ch_r_bools := VSOps.to_string right_hole_bools

let wrap ppf t =
  let ced = !current_expr_depth in
  let fpf =  fprintf ppf in
    (match t with
      | Unit -> fpf "(bExpr:unit %s %d)"
                  (ref_concat [ch_l_nums; ch_l_bools; ch_r_bools; ch_r_nums])
                  ced

      | Integer -> fpf "(bExpr:num->num %s %d)"
                     (ref_concat [ch_l_nums; ch_r_nums]) ced

      | Real -> fpf "(bExpr:num->num %s %d)"
                  (ref_concat [ch_l_nums; ch_r_nums]) ced

      | Boolean -> fpf "(bExpr:boolean %s %d)"
                     (ref_concat [ch_l_bools; ch_r_bools]) ced

      | Function (a, b) ->
        begin
          match a, b with
          | Integer, Boolean ->
            fpf "(bExpr:num->bool %s %d)"
              (ref_concat [ch_l_nums; ch_l_bools; ch_r_bools; ch_r_nums]) ced

          | Boolean, Boolean -> fpf "(bexpr:boolean %s %d)"
                                  (ref_concat [ch_l_bools; ch_r_bools]) ced

         | Integer, Integer -> fpf "(bExpr:num->num %s %d)"
                                 (ref_concat [ch_l_nums; ch_r_nums]) ced

         | _ ,_ -> fpf "(bExpr:num->num %s %d)"
                     (ref_concat [ch_l_nums; ch_l_bools; ch_r_bools; ch_r_nums])
                     ced
       end
      | _ -> fpf "(bExpr:num->num %s %d)"
               (ref_concat [ch_l_nums; ch_l_bools; ch_r_bools; ch_r_nums]) ced)


(** Pretty-printing operators *)

let string_of_unsafe_binop =
  function
  | TODO -> "TODO"

let string_of_symb_binop =
  function
  | And -> "and"
  | Nand -> "nand" | Or -> "or" | Nor -> "nor" | Implies -> "implies"
  | Xor -> "xor"
  (** Integers and reals *)
  | Plus -> "+" | Minus -> "-" | Times -> "*" | Div -> "/"
  | Quot -> "quot" | Rem -> "rem" | Mod -> "mod"
  (** Max and min *)
  | Max -> "max" | Min -> "min"
  (** Comparison *)
  | Eq -> "=" | Lt -> "<" | Le -> "<=" | Gt -> ">" | Ge -> ">="
  | Neq -> "neq"
  (** Shift*)
  | ShiftL -> "shiftl" | ShiftR -> "shiftr"
  | Expt -> "expt"
  | UnsafeBinop op -> string_of_unsafe_binop op

(** ********************************************************* UNARY OPERATORS *)
(**
   Some racket function that are otherwise unsafe
   to use in Racket, but we might still need them.
*)
let string_of_unsafe_unop =
  function
  (** Trigonometric + hyp. functions *)
  | Sin -> "sin" | Cos -> "cos" | Tan -> "tan" | Sinh -> "sinh"
  | Cosh -> "cosh" | Tanh -> "tanh"
  (** Anti functions *)
  | ASin -> "asin" | ACos -> "acos" | ATan -> "atan" | ASinh -> "asinh"
  | ACosh -> "acosh" | ATanh
  (** Other functions *)
  | Log -> "log" | Log2 -> "log2" | Log10 -> "log10"
  | Exp -> "exp" | Sqrt -> "sqrt"


let string_of_symb_unop =
  function
  | UnsafeUnop op -> string_of_unsafe_unop op
  | Not -> "not" | Add1 -> "add1" | Sub1 -> "sub1"| Abs -> "Abs"
  | Floor -> "Floor" | Ceiling -> "Ceiling"  | Truncate -> "Truncate"
  | Round -> "Round" | Neg -> "Neg" | Sgn -> "Sgn"

let ostring_of_baseSymbolicType =
  function
  | Integer -> Some "integer?"
  | Real -> Some "real?"
  | Boolean -> Some "boolean?"
  | _ -> None

let rec pp_symb_type ppf t =
  match ostring_of_baseSymbolicType t with
  | Some s -> fprintf ppf "%s" s
  | None ->
     begin
       match t with
       | Unit -> fprintf ppf "unit"
       | Tuple tl ->
          fprintf ppf "(%a)"
            (fun ppf l ->
              pp_print_list
                ~pp_sep:(fun ppf () -> fprintf ppf ",")
                (fun ppf ty -> pp_symb_type ppf ty)
                ppf
                l)
            tl

       | Bitvector  i ->
          fprintf ppf "(bitvector %i)" i

       | Function (a, b)
       | Procedure (a, b) ->
          fprintf ppf "%a->%a"
            pp_symb_type a
            pp_symb_type b

       | Pair t -> fprintf ppf "(pair %a)" pp_symb_type t

       | List (t, io) ->
          begin
            match io with
            | Some i ->
               fprintf ppf "(list %a %i)"
                 pp_symb_type t i
            | None ->
               fprintf ppf "(list %a ??)"
                 pp_symb_type t
          end

       | Vector (t, io) ->
          begin
            match io with
            | Some i ->
               fprintf ppf "(vector %a %i)"
                 pp_symb_type t i
            | None ->
               fprintf ppf "(vector %a ??)"
                 pp_symb_type t
          end

       | Box t ->
          fprintf ppf "(box %a)" pp_symb_type t

       | Struct t ->
          fprintf ppf "(struct %a)" pp_symb_type t

       | _ -> ()
     end

let rec pp_constants ppf =
  function
  | CNil -> fprintf ppf "()"
  | CInt i -> fprintf ppf "%i" i
  | CInt64 i -> fprintf ppf "%i" (Int64.to_int i)
  | CReal f -> fprintf ppf "%10.3f" f
  | CBool b -> fprintf ppf "%b" b
  | CBox cst -> fprintf ppf "<Cil.constant>"
  | CChar c -> fprintf ppf "%c" c
  | CString s -> fprintf ppf "%s" s
  | CUnop (op, c) ->
     fprintf ppf "(%s %a)" (string_of_symb_unop op) pp_constants c
  | CBinop (op, c1, c2) ->
     fprintf ppf "(%s@; %a@; %a)" (string_of_symb_binop op)
       pp_constants c1 pp_constants c2
  | CUnsafeUnop (unsop, c) -> fprintf ppf  ""
  | CUnsafeBinop (unsbop, c1, c2) -> fprintf ppf ""
  | Pi -> fprintf ppf "pi"
  | Sqrt2 -> fprintf ppf "(sqrt 2)"
  | Ln2 -> fprintf ppf "(log 2)"
  | Ln10 -> fprintf ppf "(log 10)"
  | SqrtPi -> fprintf ppf "(sqrt pi)"
  | E -> fprintf ppf "(exp 1)"

(** Basic pretty-printing *)
let rec pp_skstmt ppf ((vi, sklet) : Cil.varinfo * sklet)  =
  Format.fprintf  ppf "%s = begin @.@[%a@] end\n"
    vi.Cil.vname
    pp_sklet sklet

and pp_sklet ppf =
  function
  | SkLetExpr el ->
     fprintf ppf "@[(%s %a)@]"
       !state_struct_name
       (pp_print_list
          ~pp_sep:(fun ppf () -> fprintf ppf "@;")
          (fun ppf (v,e) -> fprintf ppf "@[<hov 2>%a@]"
            pp_skexpr e)) el

  | SkLetIn (el, l) ->
     fprintf ppf "(let @[<hov 2>(%a)@]@.@[<hov 2> %a@])"
       (fun ppf el ->
         (pp_print_list
            (fun ppf (v, e) ->
              Format.fprintf ppf "@[[%a %a]@]"
                pp_sklvar v pp_skexpr e) ppf el)) el
       pp_sklet l

and pp_sklvar (ppf : Format.formatter) sklvar =
  match sklvar with
  | SkState ->
	fprintf ppf "<s>"
  | SkVarinfo v ->
	fprintf ppf "%s" v.Cil.vname
  | SkArray (v, offset) ->
    match vi_of v with
    | Some vi ->
	   fprintf ppf "(vector-ref %a %a)" pp_sklvar v pp_skexpr offset
    | None ->
       	fprintf ppf "(vector-ref %a %a)" pp_sklvar v pp_skexpr offset

and pp_skexpr (ppf : Format.formatter) skexpr =
let fp = Format.fprintf in
  match skexpr with
  | SkVar v -> fp ppf "%a" pp_sklvar v

  | SkConst c -> fp ppf "%a" pp_constants c

  | SkFun l -> pp_sklet ppf l

  | SkApp (t, vio, argl) ->
     let funname =
       match vio with
       | Some vi -> vi.Cil.vname
       | None -> "()"
     in
     fp ppf "(%s %a)" funname
       (pp_print_list pp_skexpr) argl

  | SkHoleR t ->
     fp ppf "%a"
       wrap t

  | SkHoleL (v, t) ->
     fp ppf "%a"
       wrap t

  | SkAddrof e -> fp ppf "(AddrOf )"

  | SkAddrofLabel addr -> fp ppf "(AddrOfLabel)"

  | SkAlignof typ -> fp ppf "(AlignOf typ)"

  | SkAlignofE e -> fp ppf "(AlignOfE %a)" pp_skexpr e

  | SkBinop (op, e1, e2) ->
     fp ppf "(%s %a %a)"
        (string_of_symb_binop op) pp_skexpr e1 pp_skexpr e2

  | SkUnop (op, e) ->
     fp ppf "(%s %a)" (string_of_symb_unop op) pp_skexpr e

  | SkCond (c, e1, e2) ->
     fp ppf "(if @[%a@] @[%a@] @[%a@])"
       pp_skexpr c pp_sklet e1 pp_sklet e2

  | SkQuestion (c, e1, e2) ->
     fp ppf "(if @[%a@] @[%a@] @[%a@])"
       pp_skexpr c pp_skexpr e1 pp_skexpr e2

  | SkRec ((i, g, u), e) ->
     fp ppf "(Loop %s %s %s %a)"
       (Ct.psprint80 Cil.dn_instr i)
       (Ct.psprint80 Cil.dn_exp g)
       (Ct.psprint80 Cil.dn_instr u)
       pp_sklet e

  | SkSizeof t -> fp ppf "(SizeOf %a)" pp_symb_type t

  | SkSizeofE e -> fp ppf "(SizeOf %a)" pp_skexpr e

  | SkSizeofStr str -> fp ppf "(SizeOf %s)" str

  | SkCastE (t,e) ->
     fp ppf "(%a) %a" pp_symb_type t pp_skexpr e

  | SkStartOf l -> fp ppf "(StartOf %a)" pp_skexpr l


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
    Utils.VSOps.pvs state_set
    (pp_print_list
       ~pp_sep:(fun fmt x -> fprintf fmt "\n@.")
       pp_skstmt) stmt_li

(** Print sketches *)
let printSketch s = pp_sketch std_formatter s
let sprintSketch s =
  pp_sketch str_formatter s;
  flush_str_formatter ()

let eprintSketch s = pp_sketch err_formatter s

let pp_expr_set fmt ?(sep = (fun fmt () -> fprintf fmt "; ")) es =
  let elt_list = ES.elements es in
  if List.length elt_list = 0 then
    fprintf fmt "[Empty]"
  else
    pp_print_list ~pp_sep:sep pp_skexpr fmt elt_list

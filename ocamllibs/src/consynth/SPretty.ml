open SketchTypes
open PpHelper
open Format
open Utils
open Racket

module Ct = Utils.CilTools
module VS = Utils.VS

let print_imp_style = ref false
let printing_sketch = ref false
let holes_expr_depth = ref 1
let state_struct_name = ref "__state"
let use_non_linear_operator = ref false
let skipped_non_linear_operator = ref false

let state_vars = ref VS.empty

let reinit ?(ed = 1) ?(use_nl = false) =
  printing_sketch := false;
  holes_expr_depth := ed;
  if use_nl then
    printf "Using non-linear operators.@.";
  use_non_linear_operator := use_nl;
  skipped_non_linear_operator := false

(**
   TODO : find a way to be able to generate different hole
   expressions for R-holes and L-holes. Also, might be useful
   to refine available variables with the type of the hole.
*)
let ref_concat l = List.fold_left (fun ls s-> ls^" "^(!s)) "" l

let hole_type_expr fmt ((t, ot) : hole_type) =
  let hole_num_optype optype =
    match optype with
    | NotNum -> hole_type_name HBasicNum
    | Basic -> hole_type_name HBasicNum
    | Arith -> hole_type_name HArith
    | NonLinear ->
      if !use_non_linear_operator then
        hole_type_name HNonLinear
      else
        (skipped_non_linear_operator := true;
         hole_type_name HBasicNum)
  in
  fprintf fmt "%s"
    (match t with
     | Unit -> hole_type_name HScalarExpr

     | Integer | Real -> (hole_num_optype ot)

     | Boolean -> hole_type_name HBoolean

     | Function (a, b) ->
       begin
         match a, b with
         | Integer, Boolean -> hole_type_name HComparison

         | Boolean, Boolean -> hole_type_name HBoolean

         | Integer, Integer -> (hole_num_optype ot)

         | _ ,_ -> hole_type_name HScalarExpr

       end
     | _ -> hole_type_name HScalarExpr)

let string_of_opchoice oct =
  "(" ^ (operator_choice_name oct) ^" 0)"

(** Pretty-printing operators *)

let string_of_unsafe_binop =
  function
  | TODO -> "TODO"

let string_of_symb_binop ?(fd=false) =
  function
  | And -> "&&"
  | Nand -> "nand" | Or -> "||" | Nor -> "nor" | Implies -> "implies"
  | Xor -> "xor"
  (** Integers and reals *)
  | Plus -> "+" | Minus -> "-" | Times -> "*" | Div -> "/"
  | Quot -> "quot" | Rem -> "rem" | Mod -> "modulo"
  (** Max and min *)
  | Max -> if fd then Conf.get_conf_string "dafny_max_fun" else "max"
  | Min -> if fd then Conf.get_conf_string "dafny_min_fun" else "min"
  (** Comparison *)
  | Eq -> if fd then "==" else "="
  | Lt -> "<" | Le -> "<=" | Gt -> ">" | Ge -> ">="
  | Neq -> if fd then "!=" else "neq"
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
  | Not -> "not" | Add1 -> "add1" | Sub1 -> "sub1"| Abs -> "abs"
  | Floor -> "floor" | Ceiling -> "ceiling"  | Truncate -> "truncate"
  | Round -> "round" | Neg -> "-" | Sgn -> "sgn"

let ostring_of_baseSymbolicType =
  function
  | Integer -> Some "integer?"
  | Real -> Some "real?"
  | Boolean -> Some "boolean?"
  | _ -> None

let rec pp_symb_type ppf t =
  fprintf ppf "%s%a%s" (color "blue") pp_symb_type_aux t default
and pp_symb_type_aux ppf t =
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

let rec pp_constants ?(for_dafny=false) ppf =
  function
  | CNil -> fprintf ppf "()"
  | CInt i -> fprintf ppf "%i" i
  | CInt64 i -> fprintf ppf "%i" (Int64.to_int i)
  | CReal f -> fprintf ppf "%10.3f" f
  | CBool b ->
    if for_dafny then
      (if b then fprintf ppf "true" else fprintf ppf "false")
    else
      (if b then fprintf ppf "#t" else fprintf ppf "#f")

  | CBox cst -> fprintf ppf "<Cil.constant>"
  | CChar c -> fprintf ppf "%c" c
  | CString s -> fprintf ppf "%s" s
  | CUnop (op, c) ->
    fprintf ppf "(%s %a)" (string_of_symb_unop op)
      (pp_constants ~for_dafny:for_dafny) c
  | CBinop (op, c1, c2) ->
    if is_op_c_fun op then
      fprintf ppf "%s(%a,@; %a)" (string_of_symb_binop op)
        (pp_constants ~for_dafny:for_dafny) c1
        (pp_constants ~for_dafny:for_dafny) c2
    else
      fprintf ppf "(%s@; %a@; %a)" (string_of_symb_binop op)
        (pp_constants ~for_dafny:for_dafny) c1
        (pp_constants ~for_dafny:for_dafny) c2

  | CUnsafeUnop (unsop, c) -> fprintf ppf  ""
  | CUnsafeBinop (unsbop, c1, c2) -> fprintf ppf ""
  | Infnty -> fprintf ppf "+inf.0"
  | NInfnty -> fprintf ppf "-inf.0"
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
    fprintf ppf "@[<hov 2>(%s %a)@]"
      !state_struct_name
      (pp_print_list
         ~pp_sep:(fun ppf () -> fprintf ppf "@;")
         (fun ppf (v,e) -> fprintf ppf "@[<hov 2>%a@]"
             pp_skexpr e)) el

  | SkLetIn (el, l) ->
    fprintf ppf "@[<hov 2>(let (%a)@; %a)@]"
      (fun ppf el ->
         (pp_print_list
            (fun ppf (v, e) ->
               Format.fprintf ppf "@[<hov 2>[%a %a]@]"
                 pp_sklvar v pp_skexpr e) ppf el)) el
      pp_sklet l

and pp_sklvar (ppf : Format.formatter) sklvar =
  match sklvar with
  | SkVarinfo v ->
    fprintf ppf "%s" v.Cil.vname
  | SkArray (v, offset) ->
    let offset_str =
      fprintf str_formatter "%a" pp_skexpr offset;
      flush_str_formatter ()
    in
    if !print_imp_style then
      fprintf ppf "%a[%s]" pp_sklvar v offset_str
    else
      (fprintf ppf "(vector-ref %a %s)"
         pp_sklvar v offset_str)

  | SkTuple vs ->
    fprintf ppf "(%a)" VSOps.pvs vs

and pp_skexpr (ppf : Format.formatter) skexpr =
  let fp = Format.fprintf in
  match skexpr with
  | SkVar v -> fp ppf "%a" pp_sklvar v

  | SkConst c -> fp ppf "%a" (pp_constants ~for_dafny:false) c

  | SkFun l -> pp_sklet ppf l

  | SkApp (t, vio, argl) ->
    let funname =
      match vio with
      | Some vi -> vi.Cil.vname
      | None -> "()"
    in
    fp ppf "(%s %a)" funname
      (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt " ") pp_skexpr) argl

  | SkHoleR (t, cs) ->
    fp ppf "@[<hv 2>(%a %a %i)@]"
      hole_type_expr t CS.pp_cs cs !holes_expr_depth

  | SkHoleL (t, v, cs) ->
    fp ppf "@[<hv 2>(%a %a %i)@]"
      hole_type_expr t CS.pp_cs cs !holes_expr_depth

  | SkAddrof e -> fp ppf "(AddrOf )"

  | SkAddrofLabel addr -> fp ppf "(AddrOfLabel)"

  | SkAlignof typ -> fp ppf "(AlignOf typ)"

  | SkAlignofE e -> fp ppf "(AlignOfE %a)" pp_skexpr e

  | SkBinop (op, e1, e2) ->
    if !printing_sketch && (is_comparison_op op)
    then
      fp ppf "@[<hov 1>(%s@;%a@;%a)@]"
        (string_of_opchoice OCComparison)
        pp_skexpr e1 pp_skexpr e2
    else
      fp ppf "@[<hov 1>(%s@;%a@;%a)@]"
        (string_of_symb_binop op)
        pp_skexpr e1 pp_skexpr e2

  | SkUnop (op, e) ->
    fp ppf "@[<hov 1>(%s %a)@]"
      (string_of_symb_unop op) pp_skexpr e

  | SkCond (c, e1, e2) ->
    fp ppf "@[<hov 2>(if@;%a@;%a@;%a)@]"
      pp_skexpr c pp_sklet e1 pp_sklet e2

  | SkQuestion (c, e1, e2) ->
    if !print_imp_style then
      fp ppf "((@[%a@])? @[%a@]: @[%a@])"
        pp_skexpr c pp_skexpr e1 pp_skexpr e2
    else
      fp ppf "@[<hov 2>(if@;%a@;%a@;%a)@]"
        pp_skexpr c pp_skexpr e1 pp_skexpr e2

  | SkRec ((i, g, u), e) ->
    fp ppf "@[<hov 2>(Loop %s %s %s %a)@]"
      (Ct.psprint80 Cil.dn_instr i)
      (Ct.psprint80 Cil.dn_exp g)
      (Ct.psprint80 Cil.dn_instr u)
      pp_sklet e

  | SkSizeof t -> fp ppf "(SizeOf %a)" pp_symb_type t

  | SkSizeofE e -> fp ppf "(SizeOf %a)" pp_skexpr e

  | SkSizeofStr str -> fp ppf "(SizeOf %s)" str

  | SkCastE (t,e) ->
    fp ppf "%a" pp_skexpr e

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

let pp_expr_list fmt el =
  PpHelper.ppli fmt ~sep:" " pp_skexpr el


(**
   -----------------------------------------------------------------------------
    Pretty printing with colors and typesetting for better
    readability.
    ----------------------------------------------------------------------------
*)

let rec cp_skstmt ppf ((vi, sklet) : Cil.varinfo * sklet)  =
  Format.fprintf  ppf "%s = begin @.@[%a@] end\n"
    vi.Cil.vname
    pp_sklet sklet

and cp_sklet ppf =
  function
  | SkLetExpr el ->
    fprintf ppf "@[%s(%s%s%s%s %a%s)%s@]"
      (color "red") default
      (color "b")
      !state_struct_name
      default
      (pp_print_list
         ~pp_sep:(fun ppf () -> fprintf ppf "@;")
         (fun ppf (v,e) -> fprintf ppf "@[<hov 2>%a@]"
             cp_skexpr e)) el
      (color "red") default

  | SkLetIn (el, l) ->
    fprintf ppf "%s(%slet%s @[<hov 2>(%a)@]@.@[<hov 2> %a@]%s)%s"
      (* Opening parenthesis *)
      (color "red")
      (* Let keyword *)
      (color "b")  default
      (fun ppf el ->
         (pp_print_list
            (fun ppf (v, e) ->
               Format.fprintf ppf "@[[%a %a]@]"
                 cp_sklvar v cp_skexpr e) ppf el)) el
      cp_sklet l
      (* Closing parenthesis *)
      (color "red") default

and cp_sklvar (ppf : Format.formatter) sklvar =
  match sklvar with
  | SkVarinfo v ->
    fprintf ppf "%s%s%s" (color "yellow") v.Cil.vname default

  | SkArray (v, offset) ->
    let offset_str =
      fprintf str_formatter "%a" pp_skexpr offset;
      flush_str_formatter ()
    in
    fprintf ppf "%a[%s%s%s]" cp_sklvar v (color "i") offset_str default


  | SkTuple vs ->
    fprintf ppf "(%a)" VSOps.pvs vs

and cp_skexpr (ppf : Format.formatter) skexpr =
  let fp = Format.fprintf in
  match skexpr with
  | SkVar v -> fp ppf "%a" cp_sklvar v

  | SkConst c -> fp ppf "%s%a%s" (color "cyan")
                   (pp_constants ~for_dafny:false) c default

  | SkFun l -> cp_sklet ppf l

  | SkApp (t, vio, argl) ->
    let funname =
      match vio with
      | Some vi -> vi.Cil.vname
      | None -> "()"
    in
    fp ppf "@[<hov 1>(%s%s%s %a)@]" (color "u") funname default
      (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt " ") cp_skexpr) argl

  | SkHoleR (t, _) ->
    fp ppf "%s%a%s"
      (color "grey") hole_type_expr t default

  | SkHoleL (t, v, _) ->
    fp ppf "%s %a %s"
      (color "grey") hole_type_expr t default

  | SkAddrof e -> fp ppf "(AddrOf )"

  | SkAddrofLabel addr -> fp ppf "(AddrOfLabel)"

  | SkAlignof typ -> fp ppf "(AlignOf typ)"

  | SkAlignofE e -> fp ppf "(AlignOfE %a)" cp_skexpr e

  | SkBinop (op, e1, e2) ->
    fp ppf "@[<hov 2>(%s%s%s@;%a@;%a)@]"
      (color "b") (string_of_symb_binop op) default
      cp_skexpr e1 cp_skexpr e2

  | SkUnop (op, e) ->
    fp ppf "@[<hov 1>(%s%s%s %a)@]"
      (color "b") (string_of_symb_unop op) default cp_skexpr e

  | SkCond (c, e1, e2) ->
    fp ppf "@[<hov 1> (%sif%s@;%a@;%a@;%a)@]"
      (color "b") default
      cp_skexpr c cp_sklet e1 cp_sklet e2

  | SkQuestion (c, e1, e2) ->
    fp ppf "@[<hov 2>((%a)%s? %s%a%s %s%a)@]"
      cp_skexpr c
      (color "b") default
      cp_skexpr e1
      (color "b") default
      cp_skexpr e2

  | SkRec ((i, g, u), e) ->
    fp ppf "(Loop %s %s %s %a)"
      (Ct.psprint80 Cil.dn_instr i)
      (Ct.psprint80 Cil.dn_exp g)
      (Ct.psprint80 Cil.dn_instr u)
      cp_sklet e

  | SkSizeof t -> fp ppf "(SizeOf %a)" pp_symb_type t

  | SkSizeofE e -> fp ppf "(SizeOf %a)" cp_skexpr e

  | SkSizeofStr str -> fp ppf "(SizeOf %s)" str

  | SkCastE (t,e) ->
    fp ppf "%a" cp_skexpr e

  | SkStartOf l -> fp ppf "(StartOf %a)" cp_skexpr l


(** Print statements **)
let cprintSkstmt s = cp_skstmt std_formatter s
let scprintSkstmt s =
  cp_skstmt str_formatter s;
  flush_str_formatter ()

let ecprintSkstmt s = cp_skstmt err_formatter s

(** Print let-forms *)
let cprintSklet s = cp_sklet std_formatter s
let scprintSklet s =
  cp_sklet str_formatter s;
  flush_str_formatter ()

let ecprintSklet s = cp_sklet err_formatter s

(** Print epxressions *)
let cprintSkexpr s = cp_skexpr std_formatter s
let scprintSkexpr s =
  cp_skexpr str_formatter s;
  flush_str_formatter ()

let ecprintSkexpr s = cp_skexpr err_formatter s

let cp_expr_set fmt ?(sep = (fun fmt () -> fprintf fmt "; ")) es =
  let elt_list = ES.elements es in
  if List.length elt_list = 0 then
    fprintf fmt "[Empty]"
  else
    pp_print_list ~pp_sep:sep cp_skexpr fmt elt_list

let cp_expr_list fmt el =
  PpHelper.ppli fmt ~sep:" " cp_skexpr el



(** C-style pretty printing. Useful for printing functional intermediary
    language as a set of statements. Does more than just pretty printing,
    also check for dependencies in the list of bindings and reorder them.
*)

let printing_for_join = ref false
let cpp_class_members_set = ref VS.empty

let rec pp_c_expr ?(for_dafny = false) fmt e =
  match e with
  | SkVar v -> pp_c_var fmt v
  | SkConst c -> pp_constants ~for_dafny:for_dafny fmt c

  | SkUnop (op, e1) ->
    fprintf fmt "@[%s %a]@" (string_of_symb_unop op)
      (pp_c_expr ~for_dafny:for_dafny) e1

  | SkBinop (op, e1, e2) ->
    if is_op_c_fun op then
      fprintf fmt "@[<hov 2>%s(%a, %a)@]"
        (string_of_symb_binop ~fd:true op)
        (pp_c_expr ~for_dafny:for_dafny) e1
        (pp_c_expr ~for_dafny:for_dafny) e2
    else
      fprintf fmt "@[<hov 2>(%a %s %a)@]"
        (pp_c_expr ~for_dafny:for_dafny) e1
        (string_of_symb_binop ~fd:true op)
        (pp_c_expr ~for_dafny:for_dafny) e2

  | SkQuestion (c, e1, e2) ->
    (if for_dafny then
       fprintf fmt "@[<hov 2>if %a then@;%a else@;%a@]"
     else
       fprintf fmt "@[<hov 2>(%a ?@;%a :@;%a)@]")
      (pp_c_expr ~for_dafny:for_dafny) c (pp_c_expr ~for_dafny:for_dafny) e1
      (pp_c_expr ~for_dafny:for_dafny) e2

  | SkApp (t, vo, args) ->
    (match vo with
     | Some vi ->
       fprintf fmt "@[%s(%a)@]" vi.Cil.vname pp_c_expr_list args
     | None ->
       fprintf fmt "@[%a@]" pp_c_expr_list args)

  | SkHoleL ((t, _), v , _) -> fprintf fmt "@[<hov 2>(<LEFT_HOLE@;%a@;%a>)@]"
                                 pp_c_var v pp_typ t
  | SkHoleR ((t, _), _) -> fprintf fmt "@[<hov 2>(<RIGHT_HOLE@;%a>)@]" pp_typ t

  | _ -> fprintf fmt "@[(<UNSUPPORTED EXPRESSION %a>)@]" pp_skexpr e

and pp_c_var fmt v =
  match v with
  | SkVarinfo v ->
    let var_name =
      if !printing_for_join then
        if VSOps.has_vid v.Cil.vid !cpp_class_members_set then
          match is_right_state_varname v.Cil.vname with
          | real_varname, true, true ->
            (rs_prefix^"my_"^real_varname)
          | real_varname, true, false ->
            "my_"^real_varname
          | _ , false, _ ->
            "my_"^v.Cil.vname
        else
          v.Cil.vname
      else
        v.Cil.vname
    in
    fprintf fmt "%s" var_name

  | SkArray (v, offset) -> fprintf fmt "%a[%a]" pp_c_var v
                             (pp_c_expr ~for_dafny:false) offset
  | SkTuple vs -> fprintf fmt "(<TUPLE>)"

and pp_c_expr_list fmt el =
  PpHelper.ppli fmt ~sep:" " pp_c_expr el

let pp_c_assignment fmt (v, e) =
  fprintf fmt "@[<hov 2> %a = %a;@]" pp_c_var v (pp_c_expr ~for_dafny:false) e

let pp_c_assignment_list =
  pp_print_list
    ~pp_sep:(fun fmt () -> fprintf fmt "@;")
    pp_c_assignment

let rec pp_c_sklet fmt sklet =
  match sklet with
  | SkLetExpr assgn_list ->
    fprintf fmt "@[%a@]" pp_c_assignment_list assgn_list
  | SkLetIn (assgn_list, sklet') ->
    fprintf fmt "@[%a@;%a@]"
      pp_c_assignment_list assgn_list pp_c_sklet sklet'


let print_c_let = pp_c_sklet std_formatter
let print_c_expr = pp_c_expr std_formatter

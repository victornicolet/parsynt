open Beta
open FuncTypes
open Format
open Utils
open Racket


module Ct = Utils.CilTools
module VS = Utils.VS

let print_imp_style = ref false
let printing_sketch = ref false
let holes_expr_depth = ref 1
let use_non_linear_operator = ref false
let skipped_non_linear_operator = ref false


let state_vars = ref VS.empty

let rosette_loop_macro_name = Conf.get_conf_string "rosette_func_loop_macro_name"

let reinit ?(ed = 1) ?(use_nl = false) =
  printing_sketch := false;
  holes_expr_depth := ed;
  if use_nl then
    printf "Using non-linear operators.@.";
  use_non_linear_operator := use_nl;
  skipped_non_linear_operator := false


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


let make_index_completion_string f e =
  fprintf str_formatter "(choose (add1 %a) (sub1 %a) %a)" f e f e f e;
  flush_str_formatter ()

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

exception Not_prefix

let string_of_symb_unop ?(fc = true) ?(fd = false) =
  function
  | UnsafeUnop op -> string_of_unsafe_unop op
  | Not -> if fd || fc then "!" else "not"
  | Add1 -> if fd then "1 +" else "add1"
  | Sub1 -> if fd then "1 +" else "sub1"
  | Abs -> if fd then raise Not_prefix else "abs"
  | Floor -> if fd then raise Not_prefix else "floor"
  | Ceiling -> if fd then raise Not_prefix else "ceiling"
  | Truncate -> if fd then raise Not_prefix else "truncate"
  | Round -> if fd then raise Not_prefix else "round"
  | Neg -> "-"
  | Sgn -> if fd then raise Not_prefix else "sgn"

let string_of_unop_func ?(fc = false) ?(fd = false) op =
  try
    ignore(string_of_symb_unop ~fc:fc ~fd:fd op);
    None
  with Not_prefix ->
    Some (string_of_symb_unop ~fc:false ~fd:false op)


let ostring_of_baseSymbolicType =
  function
  | Integer -> Some "integer?"
  | Real -> Some "real?"
  | Boolean -> Some "boolean?"
  | _ -> None

open Utils.PpTools

let rec pp_symb_type ppf t =
  fprintf ppf "%s%a%s" (color "blue") pp_symb_type_aux t color_default
and pp_symb_type_aux ppf t =
  match ostring_of_baseSymbolicType t with
  | Some s -> fprintf ppf "%s" s
  | None ->
    begin
      match t with
      | Unit -> fprintf ppf "unit"
      | Record tl ->
        fprintf ppf "(%a)"
          (fun ppf l ->
             pp_print_list
               ~pp_sep:(fun ppf () -> fprintf ppf ",")
               (fun ppf (s, ty) -> fprintf ppf "%s: %a" s pp_symb_type ty)
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

let rec pp_constants ?(for_c=false) ?(for_dafny=false) ppf =
  let pp_int ppf i = fprintf ppf "%i" i in
  let pp_float ppf f = fprintf ppf "%10.3f" f in
  function
  | CNil -> fprintf ppf "()"
  | CInt i -> pp_int ppf i
  | CInt64 i -> pp_int ppf (Int64.to_int i)
  | CReal f -> pp_float ppf f
  | CBool b ->
    if for_dafny || for_c then
      (if b then fprintf ppf "true" else fprintf ppf "false")
    else
      (if b then fprintf ppf "#t" else fprintf ppf "#f")

  | CBox cst -> fprintf ppf "<Cil.constant>"
  | CChar c -> fprintf ppf "%c" c
  | CString s -> fprintf ppf "%s" s
  | CArrayInit (n, c) -> fprintf ppf "(make-list %i %a)" n (pp_constants ~for_c:for_c ~for_dafny:for_dafny) c
  | CUnop (op, c) ->
    fprintf ppf "(%s %a)" (string_of_symb_unop op)
      (pp_constants ~for_c:for_c ~for_dafny:for_dafny) c
  | CBinop (op, c1, c2) ->
    if is_op_c_fun op then
      fprintf ppf "%s(%a,@; %a)" (string_of_symb_binop op)
        (pp_constants ~for_c:for_c ~for_dafny:for_dafny) c1
        (pp_constants ~for_c:for_c ~for_dafny:for_dafny) c2
    else
      fprintf ppf "(%s@; %a@; %a)" (string_of_symb_binop op)
        (pp_constants ~for_c:for_c ~for_dafny:for_dafny) c1
        (pp_constants ~for_c:for_c ~for_dafny:for_dafny) c2

  | CUnsafeUnop (unsop, c) -> fprintf ppf  ""
  | CUnsafeBinop (unsbop, c1, c2) -> fprintf ppf ""
  | Infnty ->
    if for_dafny then
      fprintf ppf "%s" (Conf.get_conf_string "dafny_max_seq_fun")
    else
      fprintf ppf "+inf.0"
  | NInfnty ->
    if for_dafny then
      fprintf ppf "%s" (Conf.get_conf_string "dafny_min_seq_fun")
    else
      fprintf ppf "-inf.0"
  | Pi -> fprintf ppf "pi"
  | Sqrt2 -> fprintf ppf "(sqrt 2)"
  | Ln2 -> fprintf ppf "(log 2)"
  | Ln10 -> fprintf ppf "(log 10)"
  | SqrtPi -> fprintf ppf "(sqrt pi)"
  | E -> fprintf ppf "(exp 1)"

(** Basic pretty-printing *)
let rec pp_fnlvar (ppf : Format.formatter) fnlvar =
  match fnlvar with
  | FnVariable v ->
    fprintf ppf "%s" v.vname
  | FnArray (v, offset) ->
    let offset_str =
      fprintf str_formatter "%a" pp_fnexpr offset;
      flush_str_formatter ()
    in
    if !print_imp_style then
      fprintf ppf "%a[%s]" pp_fnlvar v offset_str
    else
      (fprintf ppf "(list-ref %a %s)"
         pp_fnlvar v offset_str)


and pp_fnexpr (ppf : Format.formatter) fnexpr =
  let fp = Format.fprintf in
  match fnexpr with
  | FnLetExpr el ->
    fprintf ppf "@[<hov 2>(%s %a)@]"
      (record_name ~only_by_type:true (List.map (fun (v,e) -> "_", type_of_var v) el))
      (pp_print_list
         ~pp_sep:(fun ppf () -> fprintf ppf "@;")
         (fun ppf (v,e) -> pp_fnexpr ppf e)) el

  | FnLetIn (el, l) ->
    fprintf ppf "@[<hov 2>(let (%a)@; %a)@]"
       (fun ppf el ->
          (pp_print_list
             (fun ppf (v, e) ->
                match v with
                (* For now we expect only one-dimensional arrays  *)
                | FnArray(a,i) ->
                  (match a with
                   | FnVariable _ ->
                     Format.fprintf ppf "@[<hov 2>[%a (list-set %a %a %a)]@]"
                       pp_fnlvar a pp_fnlvar a pp_fnexpr i pp_fnexpr e
                   | FnArray(a', k) ->
                     Format.fprintf ppf "@[<hov 2>[%a (list-set %a %a (list-set %a %a %a))]@]"
                       pp_fnlvar a' pp_fnlvar a' pp_fnexpr k pp_fnlvar a pp_fnexpr i pp_fnexpr e
                  )
                | _ ->
                  Format.fprintf ppf "@[<hov 2>[%a %a]@]"
                    pp_fnlvar v pp_fnexpr e)
             ppf el)) el
       pp_fnexpr l

  | FnVar v -> fp ppf "%a" pp_fnlvar v

  | FnRecord (rt, exprs) ->
    let stl =
      match rt with
      | Record stl -> stl
      | _ -> failhere __FILE__ "pp_fnexpr" "Not record type in record."
    in
    let record_name = record_name stl in
    fp ppf "(%s %a)" record_name (pp_break_sep_list pp_fnexpr) exprs

  | FnRecordMember (record, mname) ->
    let record_name =
      match type_of record with
      | Record stl -> record_name stl
      | _ -> failhere __FILE__ "pp_fnexpr" "Not record type in record member access."
    in
    fp ppf "(%s-%s %a)" record_name mname pp_fnexpr record

  | FnConst c -> fp ppf "%a" (pp_constants ~for_c:false ~for_dafny:false) c


  | FnFun l -> pp_fnexpr ppf l

  | FnVector a ->
    fprintf ppf "@[<v 2>{%a}@]"
      (fun fmt l ->
         pp_print_list
           ~pp_sep:(fun fmt () -> fprintf fmt ";@;")
           pp_fnexpr fmt l) a

  | FnArraySet(a,i,e) ->
    fprintf ppf "@[<v 2>(list-set@;%a@;%a@;%a)@]"
      pp_fnexpr a pp_fnexpr i pp_fnexpr e

  | FnApp (t, vio, argl) ->
    let funname =
      match vio with
      | Some vi -> vi.vname
      | None -> "()"
    in
    fp ppf "(%s %a)" funname
      (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt " ") pp_fnexpr) argl

  | FnHoleR (t, cs, i) ->
    let istr = make_index_completion_string pp_fnexpr i in
    fp ppf "@[<hv 2>(%a@;%a@;%i)@]"
      hole_type_expr t (CS.pp_cs istr) cs !holes_expr_depth

  | FnHoleL (t, v, cs, i) ->
    let istr = make_index_completion_string pp_fnexpr i in
    fp ppf "@[<hv 2>(%a@;%a@;%i)@]"
      hole_type_expr t (CS.pp_cs istr) cs !holes_expr_depth

  | FnChoice el ->
    fp ppf "@[<v 2>(choose@;%a)@]"
      (pp_print_list ~pp_sep:(fun fmt () -> fp fmt "@;")
         pp_fnexpr) el

  | FnAddrof e -> fp ppf "(AddrOf )"

  | FnAddrofLabel addr -> fp ppf "(AddrOfLabel)"

  | FnAlignof typ -> fp ppf "(AlignOf typ)"

  | FnAlignofE e -> fp ppf "(AlignOfE %a)" pp_fnexpr e

  | FnBinop (op, e1, e2) ->
    if !printing_sketch && (is_comparison_op op)
    then
      fp ppf "@[<hov 1>(%s@;%a@;%a)@]"
        (string_of_opchoice OCComparison)
        pp_fnexpr e1 pp_fnexpr e2
    else
      fp ppf "@[<hov 1>(%s@;%a@;%a)@]"
        (string_of_symb_binop op)
        pp_fnexpr e1 pp_fnexpr e2

  | FnUnop (op, e) ->
    fp ppf "@[<hov 1>(%s %a)@]"
      (string_of_symb_unop op) pp_fnexpr e

  | FnCond (c, e1, e2) ->
    if !print_imp_style then
      fp ppf "((@[%a@])? @[%a@]: @[%a@])"
        pp_fnexpr c pp_fnexpr e1 pp_fnexpr e2
    else
      fp ppf "@[<hov 2>(if@;%a@;%a@;%a)@]"
        pp_fnexpr c pp_fnexpr e1 pp_fnexpr e2

  | FnRec ((i, g, u), (s, k), (_s, e)) ->
    let index_set = VarSet.inter (used_in_fnexpr g) (used_in_fnexpr u) in
   ( match VarSet.cardinal index_set with
    | 0 -> fp ppf "@[<v  2>%a@]" pp_fnexpr e
    | 1 ->
      let index = VarSet.max_elt index_set in
      fp ppf "@[<hov 2>(%s %a (lambda (%s) %a)@;(lambda (%s) %a)@;%a@;(lambda (%s %s) %a))@]"
        rosette_loop_macro_name
        pp_fnexpr i
        index.vname
        (fun fmt g -> let b = !printing_sketch in
          printing_sketch := false; pp_fnexpr fmt g; printing_sketch := b)  g
        index.vname pp_fnexpr u
        pp_fnexpr k
        _s.vname
        index.vname
        pp_fnexpr e

    | _ -> failhere __FILE__ "pp_fnexpr" "Loop-function with multiple index not supported")

  | FnSizeof t -> fp ppf "(SizeOf %a)" pp_symb_type t

  | FnSizeofE e -> fp ppf "(SizeOf %a)" pp_fnexpr e

  | FnSizeofStr str -> fp ppf "(SizeOf %s)" str

  | FnCastE (t,e) ->
    fp ppf "%a" pp_fnexpr e

  | FnStartOf l -> fp ppf "(StartOf %a)" pp_fnexpr l


(** Print epxressions *)
let printFnexpr s = pp_fnexpr std_formatter s
let sprintFnexpr s =
  pp_fnexpr str_formatter s;
  flush_str_formatter ()

let eprintFnexpr s = pp_fnexpr err_formatter s

(** Print the whole intermediary pb *)
let pp_func ppf (state_set, stmt_li) =
  fprintf ppf "@[State = %a@]@;@[%a@]"
    Utils.VS.pvs state_set
    (pp_print_list
       ~pp_sep:(fun fmt x -> fprintf fmt "\n@.")
       pp_fnexpr) stmt_li

(** Print fnetches *)
let sprintFunc s = pp_func std_formatter s
let sprintFunc s =
  pp_func str_formatter s;
  flush_str_formatter ()

let eprintFnetch s = pp_func err_formatter s

let pp_expr_set fmt ?(sep = (fun fmt () -> fprintf fmt "; ")) es =
  let elt_list = ES.elements es in
  if List.length elt_list = 0 then
    fprintf fmt "[Empty]"
  else
    pp_print_list ~pp_sep:sep pp_fnexpr fmt elt_list

let pp_expr_list fmt el =
  ppli fmt ~sep:" " pp_fnexpr el


let pp_expr_map fmt em =
  fprintf fmt "@[<v>{%a}@]"
    (fun fmt em ->
       (IM.iter
        (fun k e -> fprintf fmt "%i <-- %a;@;" k pp_fnexpr e) em))
    em

(**
   -----------------------------------------------------------------------------
    Pretty printing with colors and typesetting for better
    readability.
    ----------------------------------------------------------------------------
*)
let _interp i =
  let pluses  e =
    let rec _aux (var, ints) e =
      match e with
      | FnBinop (Plus, e1, e2) ->
        let vars', ints' = _aux (var, ints) e1 in
        _aux (vars', ints') e2
      | FnConst (CInt i) -> (var, i::ints)
      | FnVar v -> (v::var, ints)
      | _ -> failwith "S"
    in
    _aux ([], []) e
  in
  try
    let vars, ints = pluses i in
    let intval = List.fold_left (+) 0 ints in
    if List.length vars = 1 then
      if intval = 0 then
        FnVar (List.hd vars)
      else
        FnBinop (Plus, FnVar (List.hd vars), FnConst (CInt intval))
    else i
  with _ -> i



let rec cp_fnlvar (ppf : Format.formatter) fnlvar =
  match fnlvar with
  | FnVariable v ->
    fprintf ppf "%s%s%s" (color "yellow") v.vname color_default

  | FnArray (v, offset) ->
    let offset_str =
      fprintf str_formatter "%a" cp_index (_interp offset);
      flush_str_formatter ()
    in
    fprintf ppf "%a[%s%s%s]" cp_fnlvar v (color "i") offset_str color_default

and cp_index fmt i =
  match i with
  | FnBinop(op, e1, e2) ->
    Format.fprintf fmt "%a%s%a"
      cp_fnexpr e1 (string_of_symb_binop op)
      cp_fnexpr e2
  | _ -> cp_fnexpr fmt i

and cp_expr_list fmt el =
  ppli fmt ~sep:"@;" cp_fnexpr el

and cp_fnexpr (ppf : Format.formatter) fnexpr =
  let fp = Format.fprintf in
  match fnexpr with
  | FnLetExpr el ->
    fprintf ppf "@[%s(%s%s%s%s %a%s)%s@]"
      (color "red") color_default
      (color "b")
      (record_name ~only_by_type:true
         (List.map (fun (v,e) -> let tv = type_of_var v in shstr_of_type tv, tv) el))
      color_default
      (pp_print_list
         ~pp_sep:(fun ppf () -> fprintf ppf "@;")
         (fun ppf (v,e) -> cp_fnexpr ppf e)) el
      (color "red") color_default

  | FnLetIn (el, l) ->
    fprintf ppf "%s(%slet%s @[<v 2>(%a)@]@.@[<hov 2> %a@]%s)%s"
      (* Opening parenthesis *)
      (color "red")
      (* Let keyword *)
      (color "b")  color_default
      (fun ppf el ->
         (pp_print_list
            (fun ppf (v, e) ->
               Format.fprintf ppf "@[[%a %a]@]"
                 cp_fnlvar v cp_fnexpr e) ppf el)) el
      cp_fnexpr l
      (* Closing parenthesis *)
      (color "red") color_default

  | FnVar v -> fp ppf "%a" cp_fnlvar v

  | FnConst c -> fp ppf "%s%a%s" (color "cyan")
                   (pp_constants ~for_c:true ~for_dafny:false) c color_default

  | FnArraySet(a,i,e) ->
    fp ppf "%a[%a] = %a" cp_fnexpr a cp_fnexpr i cp_fnexpr e

  | FnRecord (t, el) ->
    fp ppf "(Record[%a] %a)" pp_typ t cp_expr_list el

  | FnRecordMember (r, m) ->
    fp ppf "([%a]-%s %a)" pp_typ (type_of r) m cp_fnexpr r


 | FnVector a ->
    fprintf ppf "@[<v 2><%a>@]"
      (fun fmt l ->
         pp_print_list
           ~pp_sep:(fun fmt () -> fprintf fmt "; ")
           (fun fmt e -> fprintf fmt "%a" cp_fnexpr e)
           fmt l)
      a

  | FnFun l -> cp_fnexpr ppf l

  | FnApp (t, vio, argl) ->
    let funname =
      match vio with
      | Some vi -> vi.vname
      | None -> "()"
    in
    fp ppf "@[<hov 2>(%s%s%s %a)@]" (color "u") funname color_default
      (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt " ") cp_fnexpr) argl

  | FnHoleR (t, _, _) ->
    fp ppf "%s%a%s"
      (color "grey") hole_type_expr t color_default

  | FnHoleL (t, v, _, _) ->
    fp ppf "%s %a %s"
      (color "grey") hole_type_expr t color_default

  | FnChoice el ->
    fp ppf "(%sChoiceExpression%s %a)"
      (color "red") color_default pp_expr_list el

  | FnAddrof e -> fp ppf "(AddrOf )"

  | FnAddrofLabel addr -> fp ppf "(AddrOfLabel)"

  | FnAlignof typ -> fp ppf "(AlignOf typ)"

  | FnAlignofE e -> fp ppf "(AlignOfE %a)" cp_fnexpr e

  | FnBinop (op, e1, e2) ->
    begin
      match op with
      | Max | Min ->
        fp ppf "@[<hov 1>(%s%s%s@;%a@;%a)@]"
          (color "b") (string_of_symb_binop op) color_default
          cp_fnexpr e1 cp_fnexpr e2
      | _ ->
        fp ppf "@[<hov 1>(%a@;%s%s%s@;%a)@]"
          cp_fnexpr e1 (color "b") (string_of_symb_binop op)  color_default cp_fnexpr e2
    end

  | FnUnop (op, e) ->
    fp ppf "@[<hov 1>(%s%s%s %a)@]"
      (color "b") (string_of_symb_unop op) color_default cp_fnexpr e

  | FnCond (c, e1, e2) ->
    fp ppf "@[<hov 2>((%a)%s?@;%s%a%s@;%s%a)@]"
      cp_fnexpr c
      (color "b") color_default
      cp_fnexpr e1
      (color "b") color_default
      cp_fnexpr e2

  | FnRec ((i, g, u), (s, a), (_s, e)) ->
    fp ppf "(FnRec %a %a %a %a %a)"
      cp_fnexpr i
      cp_fnexpr g
      cp_fnexpr u
      cp_fnexpr a
      cp_fnexpr e

  | FnSizeof t -> fp ppf "(SizeOf %a)" pp_symb_type t

  | FnSizeofE e -> fp ppf "(SizeOf %a)" cp_fnexpr e

  | FnSizeofStr str -> fp ppf "(SizeOf %s)" str

  | FnCastE (t,e) ->
    fp ppf "%a" cp_fnexpr e

  | FnStartOf l -> fp ppf "(StartOf %a)" cp_fnexpr l

let pp_fndef fmt (func_var, args, body) =
  fprintf fmt "@[<hov 2>(define (%s@;%a)@;%a)@]"
    func_var.vname
    (fun fmt -> PpTools.pp_break_sep_list (fun fmt v -> fprintf fmt "%s" v.vname) fmt) args
    pp_fnexpr body

(** Print epxressions *)
let cprintFnexpr s = cp_fnexpr std_formatter s
let scprintFnexpr s =
  cp_fnexpr str_formatter s;
  flush_str_formatter ()

let ecprintFnexpr s = cp_fnexpr err_formatter s

let cp_expr_set fmt ?(sep = (fun fmt () -> fprintf fmt "; ")) es =
  let elt_list = ES.elements es in
  if List.length elt_list = 0 then
    fprintf fmt "[Empty]"
  else
    pp_print_list ~pp_sep:sep cp_fnexpr fmt elt_list

let cp_expr_list fmt el =
  pp_print_list
    ~pp_sep:(fun fmt () -> fprintf fmt "@;")
    cp_fnexpr
    fmt
    el

let cp_expr_map fmt em =
  fprintf fmt "@[<v>{%a}@]"
    (fun fmt em ->
       (IM.iter
        (fun k e -> fprintf fmt "%i <-- %a;@;" k cp_fnexpr e) em))
    em


(** C-style pretty printing. Useful for printing functional intermediary
    language as a set of statements. Does more than just pretty printing,
    also check for dependencies in the list of bindings and reorder them.
*)

let printing_for_join = ref false
let cpp_class_members_set = ref VarSet.empty

let rec pp_c_expr ?(for_dafny = false) fmt e =
  match e with
  | FnVar v -> pp_c_var fmt v
  | FnConst c ->
    if is_negative c then
      fprintf fmt "(%a)" (pp_constants ~for_c:true ~for_dafny:for_dafny) c
    else
      pp_constants ~for_c:true ~for_dafny:for_dafny fmt c


  (* Unary operators : some of the operators defined are not
     C operators (or Dafny ones). We have to replace them by functions. *)
  | FnUnop (op, e1) ->
    if for_dafny then
      begin
        try
          fprintf fmt "@[(%s %a)@]" (string_of_symb_unop ~fc:true ~fd:true op)
            (pp_c_expr ~for_dafny:for_dafny) e1
        with Not_prefix ->
          fprintf fmt "@[(%s(%a)@]"
            (check_option (string_of_unop_func ~fc:true ~fd:true op))
            (pp_c_expr ~for_dafny:for_dafny) e1
      end
    else
      fprintf fmt "@[(%s %a)@]" (string_of_symb_unop ~fc:true op)
        (pp_c_expr ~for_dafny:for_dafny) e1


  (* Binary operators : some of the binary operators defined
     are not C operators, so we need to define them *)

  | FnBinop (op, e1, e2) ->
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

  | FnCond (c, e1, e2) ->
    (if for_dafny then
       fprintf fmt "@[<hov 2>(if %a then@;%a else@;%a)@]"
     else
       fprintf fmt "@[<hov 2>(%a ?@;%a :@;%a)@]")
      (pp_c_expr ~for_dafny:for_dafny) c (pp_c_expr ~for_dafny:for_dafny) e1
      (pp_c_expr ~for_dafny:for_dafny) e2

  | FnApp (t, vo, args) ->
    (match vo with
     | Some vi ->
       fprintf fmt "@[%s(%a)@]" vi.vname pp_c_expr_list args
     | None ->
       fprintf fmt "@[%a@]" pp_c_expr_list args)

  | FnHoleL ((t, _), v , _, _) -> fprintf fmt "@[<hov 2>(<LEFT_HOLE@;%a@;%a>)@]"
                                 (pp_c_var ~rhs:true) v pp_typ t
  | FnHoleR ((t, _), _, _) -> fprintf fmt "@[<hov 2>(<RIGHT_HOLE@;%a>)@]" pp_typ t

  | _ -> fprintf fmt "@[(<UNSUPPORTED EXPRESSION %a>)@]" pp_fnexpr e

and pp_c_var ?(rhs = true) fmt v =
  match v with
  | FnVariable v ->
    let var_name =
      if !printing_for_join && rhs then
        if (VarSet.has_vid !cpp_class_members_set v.vid) ||
           (is_left_index_vi v) || (is_right_index_vi v) then
          match is_right_state_varname v.vname with
          | real_varname, true, true ->
            (rhs_prefix^"my_"^real_varname)
          | real_varname, true, false ->
            "my_"^real_varname
          | _ , false, _ ->
            "my_"^v.vname
        else
          v.vname
      else
        v.vname
    in
    fprintf fmt "%s" var_name

  | FnArray (v, offset) -> fprintf fmt "%a[%a]" (pp_c_var ~rhs:rhs) v
                             (pp_c_expr ~for_dafny:false) offset

and pp_c_expr_list fmt el =
  ppli fmt ~sep:" " pp_c_expr el

let pp_c_assignment fmt (v, e) =
  fprintf fmt "@[<hov 2> %a = %a;@]" (pp_c_var ~rhs:false)
    v (pp_c_expr ~for_dafny:false) e


(***********************************************************************
 * This part of the file is implemented by Raphaël Dang-Nhu for lazy computation ***********************************************************)

let globalAuxVarIndex = ref 0
(* This function generate  auxiliary variables *)
let make_Fn_Aux_Var typ = 
  let var_name = "aux"^(string_of_int !globalAuxVarIndex) in
  let var =
    { vname = var_name;
      vtype = typ;
      vid = 0;
      vistmp = false;
      vinit = None;}
  in
  globalAuxVarIndex := !globalAuxVarIndex+1;
  FnVariable var

(* This function checks if the binary operator exists in C, returns true is it does not exists *)
let check_interval_binop (op : Beta.symb_binop) (t : Beta.fn_type) = match op with
  | And -> false
  | Nand -> false
  | Or -> false
  | Nor -> false
  | Implies -> false
  | Xor -> false
  | _ -> true

(* This function prints a binary operator *)  
let print_interval_binop (t : Beta.fn_type) =
  function
  | And -> "&&"
  | Nand -> "nand" | Or -> "||" | Nor -> "nor" | Implies -> "implies"
  | Xor -> "xor"
  (** Integers and reals *)
  | Plus -> "in2_add" | Minus -> "-" | Times -> "*" | Div -> "/"
  | Quot -> "quot" | Rem -> "rem" | Mod -> "modulo"
  (** Max and min *)
  | Max -> "max"
  | Min -> "min"
  (** Comparison *)
  | Eq -> "="
  | Lt -> "in2_lt" | Le -> "in2_le" | Gt -> "in2_gt" | Ge -> "in2_ge"
  | Neq -> "neq"
  (** Shift*)
  | ShiftL -> "shiftl" | ShiftR -> "shiftr"
  | Expt -> "expt"
  | UnsafeBinop op -> string_of_unsafe_binop op

(* This function prints the type of a variable as a string (for C code generation *)
let rec print_C_type (typ : Beta.fn_type) : string = match typ with
    | Integer -> "_pos"
    | Real -> "_mm128d"
    | Boolean -> "boolean"
    | Vector (f,_) -> (print_C_type f) ^" []"
    | List _ -> "List"
    | _ -> " "

let rec print_C_type_2 (var : FuncTypes.fnLVar) : string = match var with
    | FnVariable f -> print_C_type (f.vtype)
    | FnArray (f,e) -> print_C_type_2 f^" []" 

let get_C_type (var : FuncTypes.fnLVar) : Beta.fn_type = match var with
    | FnVariable f -> f.vtype
    | _ -> failwith "Not implemented"

(* Function to print a constant *)
let rec print_interval_constant ppf =
  let pp_int ppf i = fprintf ppf "pos_create(%i)" i in
  let pp_float ppf f = fprintf ppf "in2_create(%10.3f)" f in
  function
  | CNil -> fprintf ppf "()"
  | CInt i -> pp_int ppf i
  | CInt64 i -> pp_int ppf (Int64.to_int i)
  | CReal f -> pp_float ppf f
  | CBool b ->
      (if b then fprintf ppf "true" else fprintf ppf "false")

  | CBox cst -> fprintf ppf "<Cil.constant>"
  | CChar c -> fprintf ppf "%c" c
  | CString s -> fprintf ppf "%s" s
  | CArrayInit (n, c) -> fprintf ppf "(make-list %i %a)" n print_interval_constant c
  | CUnop (op, c) ->
    fprintf ppf "(%s %a)" (string_of_symb_unop op)
      print_interval_constant  c
  | CBinop (op, c1, c2) ->
    if is_op_c_fun op then
      fprintf ppf "%s(%a,@; %a)" (string_of_symb_binop op)
        print_interval_constant c1
        print_interval_constant c2
    else
      fprintf ppf "(%s@; %a@; %a)" (string_of_symb_binop op)
        print_interval_constant c1
        print_interval_constant c2

  | CUnsafeUnop (unsop, c) -> fprintf ppf  ""
  | CUnsafeBinop (unsbop, c1, c2) -> fprintf ppf ""
  | Infnty ->
      fprintf ppf "+inf.0"
  | NInfnty ->
      fprintf ppf "-inf.0"
  | Pi -> fprintf ppf "pi"
  | Sqrt2 -> fprintf ppf "(sqrt 2)"
  | Ln2 -> fprintf ppf "(log 2)"
  | Ln10 -> fprintf ppf "(log 10)"
  | SqrtPi -> fprintf ppf "(sqrt pi)"
  | E -> fprintf ppf "(exp 1)"

(* This function returns the expected type, according to a result type and a unary operation *)
let expectedTypeUn (op : Beta.symb_unop) (v : FuncTypes.fnLVar) : fn_type = match v with
    | FnVariable f -> (match (f.vtype,op) with
        | (Integer,_) -> Integer
        | (Real,_) -> Real
        | (Boolean,_) -> Boolean
        | _ -> failwith "Case not implemented yet"
    )
    | _ -> failwith "Not implemented for array"

let expectedType (op : Beta.symb_binop) (v : FuncTypes.fnLVar) : fn_type*fn_type = match v with
    | FnVariable f -> (match (f.vtype,op) with
        | (Integer,_) -> (Integer,Integer)
        | (Real,_) -> (Real,Real)
        | (Boolean,Eq) -> (Real,Real)
        | (Boolean,Lt) -> (Real,Real)
        | (Boolean,Le) -> (Real,Real)
        | (Boolean,Gt) -> (Real,Real)
        | (Boolean,Ge) -> (Real,Real)
        | (Boolean,Neq) -> (Real,Real)
        | (Boolean,_) -> (Boolean,Boolean)
        | _ -> failwith "Case not implemented yet"
    )
    | _ -> failwith "Not implemented for array"

(* This function prints an assignment *)
let rec print_interval_assignment fmt (v, e) =
  match e with
  | FnVar evar -> 
  fprintf fmt "@[<v>%a = %a;@]" (pp_c_var ~rhs:false)
    v (pp_c_var ~rhs:false) evar
  | FnConst c ->
    if is_negative c then
  fprintf fmt "@[<v>%a = (%a);@]" (pp_c_var ~rhs:false)
    v print_interval_constant c
    else
  fprintf fmt "@[<v>%a = %a;@]" (pp_c_var ~rhs:false)
    v print_interval_constant c


  (* Unary operators : some of the operators defined are not
     C operators. We have to replace them by functions. *)
  | FnUnop (op, e1) ->
    let t = expectedTypeUn op v in
    let auxVar = make_Fn_Aux_Var t in 
    fprintf fmt "@[<v>%a @ %a = (%s %a);@]"
    print_interval_declaration (auxVar,e1)
    (pp_c_var ~rhs:false) v
    (string_of_symb_unop ~fc:true op)
    (pp_c_var ~rhs:false) auxVar


  (* Binary operators : some of the binary operators defined
     are not C operators, so we need to define them *)

  | FnBinop (op, e1, e2) ->
    if check_interval_binop op (get_C_type v) then
        let (t1,t2) = expectedType op v in
        let auxVar = make_Fn_Aux_Var t1 in 
        let auxVar0 = make_Fn_Aux_Var t2 in 
        fprintf fmt "@[<v>%a @%a @%a = %s(%a,%a);@]"
        print_interval_declaration (auxVar,e1)
        print_interval_declaration (auxVar0,e2)
        (pp_c_var ~rhs:false) v
        (print_interval_binop (get_C_type v) op)
        (pp_c_var ~rhs:false) auxVar
        (pp_c_var ~rhs:false) auxVar0

    else
        let (t1,t2) = expectedType op v in
        let auxVar = make_Fn_Aux_Var t1 in 
        let auxVar0 = make_Fn_Aux_Var t2 in 
        fprintf fmt "@[<v>%a @ %a @ %a = (%a %s %a);@]"
        print_interval_declaration (auxVar,e1)
        print_interval_declaration (auxVar0,e2)
        (pp_c_var ~rhs:false) v
        (pp_c_var ~rhs:false) auxVar
        (print_interval_binop (get_C_type v) op)
        (pp_c_var ~rhs:false) auxVar0

  | FnCond (c, e1, e2) ->
        let auxVar = make_Fn_Aux_Var Boolean in 
        let t = get_C_type v in
        (match t with 
            | Integer ->
                let undefAuxVar = make_Fn_Aux_Var t in 
                let undefAuxVar0 = make_Fn_Aux_Var t in 
                fprintf fmt "@[<v>%a @ @ if (%a == True) {@;<0 2>@[<v>%a @] @ } else if (%a == False) {@;<0 2>@[<v>%a @] @ } else if (%a == Undefined) {@;<0 2>@[<v>%a @ %a @ %a = pos_merge(%a,%a) @] @ } @ @ @]"
                print_interval_declaration (auxVar,c)
                (pp_c_var ~rhs:false) auxVar
                print_interval_assignment (v,e1)
                (pp_c_var ~rhs:false) auxVar
                print_interval_assignment (v,e2)
                (pp_c_var ~rhs:false) auxVar
                print_interval_declaration (undefAuxVar,e1)
                print_interval_declaration (undefAuxVar0,e1)
                (pp_c_var ~rhs:false) v
                (pp_c_var ~rhs:false) undefAuxVar
                (pp_c_var ~rhs:false) undefAuxVar0
            | Real ->
                let undefAuxVar = make_Fn_Aux_Var t in 
                let undefAuxVar0 = make_Fn_Aux_Var t in 
                fprintf fmt "@[<v>%a @ @ if (%a == True) {@;<0 2>@[<v>%a @] @ } else if (%a == False) {@;<0 2>@[<v>%a @] @ } else if (%a == Undefined) {@;<0 2>@[<v>%a @ %a @ %a = in2_merge(%a,%a)] @ } @ @ @]"
                print_interval_declaration (auxVar,c)
                (pp_c_var ~rhs:false) auxVar
                print_interval_assignment (v,e1)
                (pp_c_var ~rhs:false) auxVar
                print_interval_assignment (v,e2)
                (pp_c_var ~rhs:false) auxVar
                print_interval_declaration (undefAuxVar,e1)
                print_interval_declaration (undefAuxVar0,e1)
                (pp_c_var ~rhs:false) v
                (pp_c_var ~rhs:false) undefAuxVar
                (pp_c_var ~rhs:false) undefAuxVar0
            | _ -> failwith "Not yet implemented") 

  | FnApp (t, vo, args) ->
    (match vo with
     | Some vi ->
       fprintf fmt "@[%s(%a)@]" vi.vname pp_c_expr_list args
     | None ->
       fprintf fmt "@[%a@]" pp_c_expr_list args)

  | _ -> fprintf fmt "@[(<UNSUPPORTED EXPRESSION %a>)@]" pp_fnexpr e

(* This function prints a declaration *)
and print_interval_declaration fmt (v, e) =
  match e with
  | FnVar evar -> 
  fprintf fmt "@[<v>%s %a = %a;@]"
    (print_C_type_2 v)
  (pp_c_var ~rhs:false)
    v (pp_c_var ~rhs:false) evar
  | FnConst c ->
    if is_negative c then
  fprintf fmt "@[<v>%s %a = (%a);@]"
    (print_C_type_2 v)
    (pp_c_var ~rhs:false) v
    print_interval_constant c
    else
  fprintf fmt "@[<v>%s %a = %a;@]"
    (print_C_type_2 v)
    (pp_c_var ~rhs:false) v
    print_interval_constant c


  (* Unary operators : some of the operators defined are not
     C operators. We have to replace them by functions. *)
  | FnUnop (op, e1) ->
    let t = expectedTypeUn op v in
    let auxVar = make_Fn_Aux_Var t in 
    fprintf fmt "@[<v>%a @ %s %a = (%s %a);@]"
    print_interval_declaration (auxVar,e1)
    (print_C_type_2 v)
    (pp_c_var ~rhs:false) v
    (string_of_symb_unop ~fc:true op)
    (pp_c_var ~rhs:false) auxVar


  (* Binary operators : some of the binary operators defined
     are not C operators, so we need to define them *)

  | FnBinop (op, e1, e2) ->
    if check_interval_binop op (get_C_type v) then
        let (t1,t2) = expectedType op v in
        let auxVar = make_Fn_Aux_Var t1 in 
        let auxVar0 = make_Fn_Aux_Var t2 in 
        fprintf fmt "@[<v>%a@ %a@ %s %a = %s(%a,%a);@]"
        print_interval_declaration (auxVar,e1)
        print_interval_declaration (auxVar0,e2)
        (print_C_type_2 v)
        (pp_c_var ~rhs:false) v
        (print_interval_binop (get_C_type v) op)
        (pp_c_var ~rhs:false) auxVar
        (pp_c_var ~rhs:false) auxVar0

    else
        let (t1,t2) = expectedType op v in
        let auxVar = make_Fn_Aux_Var t1 in 
        let auxVar0 = make_Fn_Aux_Var t2 in 
        fprintf fmt "@[<v>%a@ %a@ %s %a = (%a %s %a);@]"
        print_interval_declaration (auxVar,e1)
        print_interval_declaration (auxVar0,e2)
        (print_C_type_2 v)
        (pp_c_var ~rhs:false) v
        (pp_c_var ~rhs:false) auxVar
        (print_interval_binop (get_C_type v) op)
        (pp_c_var ~rhs:false) auxVar0

  | FnCond (c, e1, e2) ->
        let auxVar = make_Fn_Aux_Var Boolean in 
        fprintf fmt "@[<v>%a @ if (%a == True) {@ @[<v>%a@]} else if (%a == False) { @;<2>%a @ } else if (%a == Undefined) { @;<2>%a @ }@]"
    print_interval_declaration (auxVar,c)
    (pp_c_var ~rhs:false) auxVar
    print_interval_declaration (v,e1)
    (pp_c_var ~rhs:false) auxVar
    print_interval_declaration (v,e2)
    (pp_c_var ~rhs:false) auxVar
    print_interval_declaration (v,e1)

  | FnApp (t, vo, args) ->
    (match vo with
     | Some vi ->
       fprintf fmt "@[%s(%a)@]" vi.vname pp_c_expr_list args
     | None ->
       fprintf fmt "@[%a@]" pp_c_expr_list args)

  | _ -> fprintf fmt "@[(<UNSUPPORTED EXPRESSION %a>)@]" pp_fnexpr e

(***************************************************************
 * End of added part ******************************************)

let pp_c_assignment_list p_id_asgn_list fmt ve_list =
  let filtered_ve_list =
    List.filter
      (fun (v,e) ->
         match e with
         | FnVar v' when v = v' -> false
         | _ -> true)
      ve_list
  in
  pp_print_list
    ~pp_sep:(fun fmt () -> fprintf fmt "@;")
    print_interval_assignment
    fmt
    (if p_id_asgn_list then ve_list else filtered_ve_list)

let rec pp_c_fnlet ?(p_id_assign = true) fmt fnlet =
  match fnlet with
  | FnLetExpr assgn_list ->
    fprintf fmt "@[%a@]" (pp_c_assignment_list p_id_assign) assgn_list
  | FnLetIn (assgn_list, fnlet') ->
    fprintf fmt "@[%a@;%a@]"
      (pp_c_assignment_list p_id_assign) assgn_list
      (pp_c_fnlet ~p_id_assign:p_id_assign) fnlet'
  | _ -> ()


let print_c_let = pp_c_fnlet std_formatter
let print_c_expr = pp_c_expr std_formatter

let rec pp_problem_rep fmt fnetch =
  fprintf fmt "@[<v 2>%s%sSummary for %s (%i) :%s@;\
               %sLoop body :%s@;%a@;\
               %sJoin:%s@;%a\n @;\
               %s%a%s@]"
    (color "black") (color "b-green")
    fnetch.loop_name fnetch.id
    color_default
    (color "b") color_default
    pp_fnexpr fnetch.main_loop_body
    (color "b") color_default
    pp_fnexpr fnetch.join_solution
    (color "b-lightgray")
    (fun fmt () ->
       if List.length fnetch.inner_functions > 0 then
         fprintf fmt "@[<v 2>%sInner functions:%s\n@;%a@]"
           (color "b-blue") color_default
           (pp_print_list ~pp_sep:pp_sep_brk pp_problem_rep)
           fnetch.inner_functions
       else
         ()) ()
  color_default;

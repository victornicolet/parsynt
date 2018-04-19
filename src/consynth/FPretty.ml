open FuncTypes
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
      (fprintf ppf "(vector-ref %a %s)"
         pp_fnlvar v offset_str)

  | FnTuple vs ->
    if VarSet.cardinal vs > 1 then
      fprintf ppf "(values %a)" VarSet.pp_var_names vs
    else
      fprintf ppf "%a" VarSet.pp_var_names vs

and pp_fnexpr (ppf : Format.formatter) fnexpr =
  let fp = Format.fprintf in
  match fnexpr with
  | FnLetExpr el ->
    fprintf ppf "@[<hov 2>(%s %a)@]"
      !state_struct_name
      (pp_print_list
         ~pp_sep:(fun ppf () -> fprintf ppf "@;")
         (fun ppf (v,e) -> fprintf ppf "@[<hov 2>%a@]"
             pp_fnexpr e)) el

  | FnLetIn (el, l) ->
    (match el with
    | [(FnArray(a,i), e)] ->
      (fprintf ppf "@[<v>(vector-set! %a %a %a)@;%a@]"
         pp_fnlvar a pp_fnexpr i pp_fnexpr e pp_fnexpr l)
    | _ ->
      (fprintf ppf "@[<hov 2>(let (%a)@; %a)@]"
         (fun ppf el ->
            (pp_print_list
               (fun ppf (v, e) ->
                  Format.fprintf ppf "@[<hov 2>[%a %a]@]"
                    pp_fnlvar v pp_fnexpr e) ppf el)) el
         pp_fnexpr l))

  | FnVar v -> fp ppf "%a" pp_fnlvar v

  | FnConst c -> fp ppf "%a" (pp_constants ~for_c:false ~for_dafny:false) c

  | FnFun l -> pp_fnexpr ppf l

  | FnVector a ->
    fprintf ppf "@[<v 2><%a>@]"
      (fun fmt l ->
         pp_print_list
           ~pp_sep:(fun fmt () -> fprintf fmt "; @;")
           pp_fnexpr fmt l)
      (Array.to_list a)

  | FnApp (t, vio, argl) ->
    let funname =
      match vio with
      | Some vi -> vi.vname
      | None -> "()"
    in
    fp ppf "(%s %a)" funname
      (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt " ") pp_fnexpr) argl

  | FnHoleR (t, cs) ->
    fp ppf "@[<hv 2>(%a %a %i)@]"
      hole_type_expr t CS.pp_cs cs !holes_expr_depth

  | FnHoleL (t, v, cs) ->
    fp ppf "@[<hv 2>(%a %a %i)@]"
      hole_type_expr t CS.pp_cs cs !holes_expr_depth

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

  | FnRec ((i, g, u), e) ->
    fp ppf "@[<hov 2>(Loop %s %s %s %a)@]"
      (Ct.psprint80 Cil.dn_instr i)
      (Ct.psprint80 Cil.dn_exp g)
      (Ct.psprint80 Cil.dn_instr u)
      pp_fnexpr e

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


(**
   -----------------------------------------------------------------------------
    Pretty printing with colors and typesetting for better
    readability.
    ----------------------------------------------------------------------------
*)

let rec cp_fnlvar (ppf : Format.formatter) fnlvar =
  match fnlvar with
  | FnVariable v ->
    fprintf ppf "%s%s%s" (color "yellow") v.vname color_default

  | FnArray (v, offset) ->
    let offset_str =
      fprintf str_formatter "%a" pp_fnexpr offset;
      flush_str_formatter ()
    in
    fprintf ppf "%a[%s%s%s]" cp_fnlvar v (color "i") offset_str color_default


  | FnTuple vs ->
    fprintf ppf "@[<v 2>(%a)@]" VarSet.pp_var_names vs

and cp_fnexpr (ppf : Format.formatter) fnexpr =
  let fp = Format.fprintf in
  match fnexpr with
  | FnLetExpr el ->
    fprintf ppf "@[%s(%s%s%s%s %a%s)%s@]"
      (color "red") color_default
      (color "b")
      !state_struct_name
      color_default
      (pp_print_list
         ~pp_sep:(fun ppf () -> fprintf ppf "@;")
         (fun ppf (v,e) -> fprintf ppf "@[<v 2>%a@]"
             cp_fnexpr e)) el
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

 | FnVector a ->
    fprintf ppf "@[<v 2><%a>@]"
      (fun fmt l ->
         pp_print_list
           ~pp_sep:(fun fmt () -> fprintf fmt "; @;")
           cp_fnexpr fmt l)
      (Array.to_list a)

  | FnFun l -> cp_fnexpr ppf l

  | FnApp (t, vio, argl) ->
    let funname =
      match vio with
      | Some vi -> vi.vname
      | None -> "()"
    in
    fp ppf "@[<hov 2>(%s%s%s %a)@]" (color "u") funname color_default
      (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt " ") cp_fnexpr) argl

  | FnHoleR (t, _) ->
    fp ppf "%s%a%s"
      (color "grey") hole_type_expr t color_default

  | FnHoleL (t, v, _) ->
    fp ppf "%s %a %s"
      (color "grey") hole_type_expr t color_default

  | FnAddrof e -> fp ppf "(AddrOf )"

  | FnAddrofLabel addr -> fp ppf "(AddrOfLabel)"

  | FnAlignof typ -> fp ppf "(AlignOf typ)"

  | FnAlignofE e -> fp ppf "(AlignOfE %a)" cp_fnexpr e

  | FnBinop (op, e1, e2) ->
    fp ppf "@[<hov 1>(%s%s%s@;%a@;%a)@]"
      (color "b") (string_of_symb_binop op) color_default
      cp_fnexpr e1 cp_fnexpr e2

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

  | FnRec ((i, g, u), e) ->
    fp ppf "(Loop %s %s %s %a)"
      (Ct.psprint80 Cil.dn_instr i)
      (Ct.psprint80 Cil.dn_exp g)
      (Ct.psprint80 Cil.dn_instr u)
      cp_fnexpr e

  | FnSizeof t -> fp ppf "(SizeOf %a)" pp_symb_type t

  | FnSizeofE e -> fp ppf "(SizeOf %a)" cp_fnexpr e

  | FnSizeofStr str -> fp ppf "(SizeOf %s)" str

  | FnCastE (t,e) ->
    fp ppf "%a" cp_fnexpr e

  | FnStartOf l -> fp ppf "(StartOf %a)" cp_fnexpr l


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

  | FnHoleL ((t, _), v , _) -> fprintf fmt "@[<hov 2>(<LEFT_HOLE@;%a@;%a>)@]"
                                 (pp_c_var ~rhs:true) v pp_typ t
  | FnHoleR ((t, _), _) -> fprintf fmt "@[<hov 2>(<RIGHT_HOLE@;%a>)@]" pp_typ t

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
            (rs_prefix^"my_"^real_varname)
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
  | FnTuple vs -> fprintf fmt "(<TUPLE>)"

and pp_c_expr_list fmt el =
  ppli fmt ~sep:" " pp_c_expr el

let pp_c_assignment fmt (v, e) =
  fprintf fmt "@[<hov 2> %a = %a;@]" (pp_c_var ~rhs:false)
    v (pp_c_expr ~for_dafny:false) e

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
    pp_c_assignment
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
    pp_fnexpr fnetch.loop_body
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

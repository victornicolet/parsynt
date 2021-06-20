open Beta
open Fn
open Format
open Fmt
open Sygus.Racket
open Utils

let print_imp_style = ref false
let printing_sketch = ref false

let use_non_linear_operator = ref false
let skipped_non_linear_operator = ref false
let assume_join_map = ref true

let state_vars = ref VarSet.empty

let rosette_loop_macro_name =
  Option.value ~default:"LoopFunc"
  (Config.get_conf_string "rosette_func_loop_macro_name")

let reinit _ed use_nl =
  printing_sketch := false;

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
  if !assume_join_map then
    begin
      fprintf str_formatter "%a" f e;
      flush_str_formatter ()
    end
  else
    begin
      fprintf str_formatter "(choose (add1 %a) (sub1 %a) %a)" f e f e f e;
      flush_str_formatter ()
    end


let rec pp_symb_type ppf t =
  Fmt.pf ppf "%a" (styled (`Fg `Blue) pp_symb_type_aux) t 
and pp_symb_type_aux ppf t =
  match ostring_of_baseSymbolicType t with
  | Some s -> fprintf ppf "%s" s
  | None ->
    begin
      match t with
      | Unit -> fprintf ppf "unit"
      | Record (s, tl) ->
        fprintf ppf "(%s | %a)"
          s
          (fun ppf l ->
             pp_print_list
               ~pp_sep:(fun ppf () -> fprintf ppf ",")
               (fun ppf (s, ty) -> fprintf ppf "%s: %a" s pp_symb_type ty)
               ppf
               l) tl

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
  let fp = pf in
  match fnexpr with
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
                     Format.fprintf ppf
                       "@[<hov 2>[%a (list-set %a %a (list-set %a %a %a))]@]"
                       pp_fnlvar a' pp_fnlvar a' pp_fnexpr k pp_fnlvar
                       a pp_fnexpr i pp_fnexpr e
                  )
                | _ ->
                  Format.fprintf ppf "@[<hov 2>[%a %a]@]"
                    pp_fnlvar v pp_fnexpr e)
             ppf el)) el
       pp_fnexpr l

  | FnVar v -> fp ppf "%a" pp_fnlvar v

  | FnRecord (vs, exprs) ->
    let rname = record_name vs in
    fp ppf "@[<v 2>(%s@;%a)@]" rname (list ~sep:sp pp_fnexpr)
      (snd (Base.List.unzip (unwrap_state vs exprs)))

  | FnRecordMember (record, mname) ->
    let record_name =
      match type_of record with
      | Record (name, _) -> name
      | _ -> failhere __FILE__ "pp_fnexpr"
               "Not a record type in record member access."
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

  | FnApp (_, vio, argl) ->
    let funname =
      match vio with
      | Some vi -> vi.vname
      | None -> "()"
    in
    fp ppf "(%s %a)" funname
      (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt " ") pp_fnexpr) argl

  | FnHoleR (t, cs, i, d) ->
    if CS.is_empty cs then
      fp ppf "(??)"
    else
      let istr = make_index_completion_string pp_fnexpr i in
      fp ppf "@[<hv 2>(%a@;%a@;%i)@]"
        hole_type_expr t (CS.pp_cs istr) cs d

  | FnHoleL (t, _, cs, i, d) ->
    if CS.is_empty cs then
      fp ppf "(??)"
    else
      let istr = make_index_completion_string pp_fnexpr i in
      fp ppf "@[<hv 2>(%a@;%a@;%i)@]"
        hole_type_expr t (CS.pp_cs istr) cs d

  | FnChoice el ->
    fp ppf "@[<v 2>(choose@;%a)@]"
      (pp_print_list ~pp_sep:(fun fmt () -> fp fmt "@;")
         pp_fnexpr) el

  | FnAddrof _ -> fp ppf "(AddrOf )"  

  | FnAlignof _ -> fp ppf "(AlignOf typ)"

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

  | FnRec ((i, g, u), (_, k), (_s, e)) ->
    let index_set = used_in_fnexpr u in
   ( match VarSet.cardinal index_set with
     | 0 ->
       fp ppf "@[<hov 2>(%s %a (lambda () %a)@;(lambda () %a)@;%a@;(lambda (%s) %a))@]"
         rosette_loop_macro_name
         pp_fnexpr i
         (fun fmt g -> let b = !printing_sketch in
           printing_sketch := false; pp_fnexpr fmt g; printing_sketch := b)  g
         pp_fnexpr u
         pp_fnexpr k
         _s.vname
         pp_fnexpr e

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

  | FnCastE (_,e) ->
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
    VarSet.pp_vs state_set
    (list
       ~sep:(fun fmt _ -> fprintf fmt "\n@.")
       pp_fnexpr) stmt_li

(** Print fnetches *)
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

let pp_expr_list =
  list ~sep:sp pp_fnexpr


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
    fprintf ppf "%a" (styled (`Fg `Yellow) string) v.vname

  | FnArray (v, offset) ->
    let offset_str =
      fprintf str_formatter "%a" cp_index (_interp offset);
      flush_str_formatter ()
    in
    fprintf ppf "%a[%a]" cp_fnlvar v (styled (`Fg `Cyan) string) offset_str

and cp_index fmt i =
  match i with
  | FnBinop(op, e1, e2) ->
    Format.fprintf fmt "%a%s%a"
      cp_fnexpr e1 (string_of_symb_binop op)
      cp_fnexpr e2
  | _ -> cp_fnexpr fmt i

and cp_expr_list fmt el = list ~sep:sp cp_fnexpr fmt el

and cp_fnexpr (ppf : Format.formatter) fnexpr =
  match fnexpr with
  | FnLetIn (el, l) ->
    pf ppf "%a%a@;@[<v 2>(%a)@]@.@[<hov 2> %a@]%a"
      (* Opening parenthesis *)
      (styled (`Fg `Red) string) "("
      (* Let keyword *)
      (styled (`Fg `Blue) string) "let"
      (fun ppf el ->
         (pp_print_list
            (fun ppf (v, e) ->
               Format.fprintf ppf "@[[%a %a]@]"
                 cp_fnlvar v cp_fnexpr e) ppf el)) el
      cp_fnexpr l
      (* Closing parenthesis *)
      (styled (`Fg `Red) string) ")"

  | FnVar v -> pf ppf "%a" cp_fnlvar v

  | FnConst c -> pf ppf "%a"
                   (styled (`Fg `Cyan) (pp_constants ~for_c:true ~for_dafny:false))
                    c

  | FnArraySet(a,i,e) ->
    pf ppf "%a[%a] = %a" cp_fnexpr a cp_fnexpr i cp_fnexpr e

  | FnRecord (vs, emap) ->
    pf ppf "(Record[%s] %a)" (record_name vs)
      cp_expr_list (snd (Base.List.unzip (unwrap_state vs emap)))

  | FnRecordMember (r, m) ->
    pf ppf "([%a]-%s %a)" pp_typ (type_of r) m cp_fnexpr r


 | FnVector a ->
    pf ppf "@[<v><%a>@]"
      (fun fmt l ->
         pp_print_list
           ~pp_sep:(fun fmt () -> fprintf fmt ";@;")
           (fun fmt e -> fprintf fmt "%a" cp_fnexpr e)
           fmt l)
      a

  | FnFun l -> cp_fnexpr ppf l

  | FnApp (_, vio, argl) ->
    let funname =
      match vio with
      | Some vi -> vi.vname
      | None -> "()"
    in
    pf ppf "@[<hov 2>(%a %a)@]" (styled `Underline string) funname 
      (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt " ") cp_fnexpr) argl

  | FnHoleR (t, _, _, _) ->
    pf ppf "%a" (styled (`Fg `Magenta) hole_type_expr) t

  | FnHoleL (t, _, _, _, _) ->
    pf ppf "%a"  (styled (`Fg `Magenta) hole_type_expr) t

  | FnChoice el ->
    pf ppf "(%a %a)"
      (styled (`Fg `Red) string) "ChoiceExpression" pp_expr_list el

  | FnAddrof _ -> pf ppf "(AddrOf )"

  | FnAlignof _ -> pf ppf "(AlignOf typ)"

  | FnAlignofE e -> pf ppf "(AlignOfE %a)" cp_fnexpr e

  | FnBinop (op, e1, e2) ->
    begin
      match op with
      | Max | Min ->
        pf ppf "@[<hov 1>(%a@;%a@;%a)@]"
          (styled (`Fg `Blue) string) (string_of_symb_binop op)
          cp_fnexpr e1 cp_fnexpr e2
      | _ ->
        pf ppf "@[<hov 1>(%a@;%a@;%a)@]"
          cp_fnexpr e1 
          (styled (`Fg `Blue) string)
           (string_of_symb_binop op) 
           cp_fnexpr e2
    end

  | FnUnop (op, e) ->
    pf ppf "@[<hov 1>(%a %a)@]"
    (styled (`Fg `Blue) string) (string_of_symb_unop op)
      cp_fnexpr e

  | FnCond (c, e1, e2) ->
    pf ppf "@[<hov 2>((%a)?@;%a:@;%a)@]"
      cp_fnexpr c
      cp_fnexpr e1
      cp_fnexpr e2

  | FnRec ((i, g, u), (_, a), (_s, e)) ->
    pf ppf "(FnRec %a %a %a %a %a)"
      cp_fnexpr i
      cp_fnexpr g
      cp_fnexpr u
      cp_fnexpr a
      cp_fnexpr e

  | FnSizeof t -> pf ppf "(SizeOf %a)" pp_symb_type t

  | FnSizeofE e -> pf ppf "(SizeOf %a)" cp_fnexpr e

  | FnSizeofStr str -> pf ppf "(SizeOf %s)" str

  | FnCastE (_,e) ->
    pf ppf "%a" cp_fnexpr e

  | FnStartOf l -> pf ppf "(StartOf %a)" cp_fnexpr l

let pp_fndef fmt (func_var, args, body) =
  fprintf fmt "@[<hov 2>(define (%s@;%a)@;%a)@]"
    func_var.vname
    (fun fmt -> list ~sep:sp (fun fmt v -> fprintf fmt "%s" v.vname) fmt) args
    pp_fnexpr body

(** Print epxressions *)
let cprintFnexpr s = cp_fnexpr std_formatter s
let scprintFnexpr s =
  cp_fnexpr str_formatter s;
  flush_str_formatter ()

let ecprintFnexpr s = cp_fnexpr err_formatter s

let cp_expr_set ?(sep = (fun fmt () -> fprintf fmt "; ")) fmt es =
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

  | FnApp (_, vo, args) ->
    (match vo with
     | Some vi ->
       fprintf fmt "@[%s(%a)@]" vi.vname pp_c_expr_list args
     | None ->
       fprintf fmt "@[%a@]" pp_c_expr_list args)

  | FnHoleL ((t, _), v , _, _, _) -> fprintf fmt "@[<hov 2>(<LEFT_HOLE@;%a@;%a>)@]"
                                 (pp_c_var ~rhs:true) v pp_typ t
  | FnHoleR ((t, _), _, _, _) -> fprintf fmt "@[<hov 2>(<RIGHT_HOLE@;%a>)@]" pp_typ t

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
  list ~sep:sp pp_c_expr fmt el

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
  | FnLetIn (assgn_list, fnlet') ->
    fprintf fmt "@[%a@;%a@]"
      (pp_c_assignment_list p_id_assign) assgn_list
      (pp_c_fnlet ~p_id_assign:p_id_assign) fnlet'
  | _ -> ()


let print_c_let = pp_c_fnlet std_formatter
let print_c_expr = pp_c_expr std_formatter

let rec pp_problem_rep ?(inner=false) fmt fnetch =
  fprintf fmt "@[<v 2>%a@;\
               Loop body :@;%a@;\
               Join:@;%a\n @;\
               %a@]"
    (styled (`Bg `Green) 
      (fun ppf (s,i) -> pf ppf "Summary for %s (%i) :" s i))
    (fnetch.loop_name, fnetch.id)
    pp_fnexpr fnetch.main_loop_body
    pp_fnexpr
    (if inner then fnetch.memless_solution else fnetch.join_solution)
    (fun fmt () ->
       if List.length fnetch.inner_functions > 0 then
         fprintf fmt "@[<v 2>Inner functions:\n@;%a@]"
           (list ~sep:sp (pp_problem_rep ~inner:true))
           fnetch.inner_functions
       else
         ()) ();;

let pp_func_dec fmt funcdec =
  let pp_args =
    list ~sep:comma
       (fun fmt arg -> fprintf fmt "%a %s" pp_typ arg.vtype arg.vname)
  in
  fprintf fmt "@[<v 4>%a %s@;(%a)@;[%a]@]"
    pp_typ funcdec.fvar.vtype funcdec.fvar.vname
    pp_args funcdec.fformals pp_args funcdec.flocals

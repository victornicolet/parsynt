open Cil
open Format
open Utils
open SketchTypes
open SPretty



type type_simple
type type_composed

type _ dafny_basic_type =
  | Int : type_simple dafny_basic_type
  | Real: type_simple dafny_basic_type
  | Bool: type_simple dafny_basic_type
  | Bottom : type_simple dafny_basic_type
  | Sequence: type_simple dafny_basic_type -> type_composed dafny_basic_type


let rec string_of_dt : type a. a dafny_basic_type -> string =
  function
  | Sequence t -> (fprintf str_formatter
                     "seq<%s>" (string_of_dt t);
                   flush_str_formatter ())
  | Int -> "int"
  | Real -> "real"
  | Bool -> "bool"
  | Bottom -> "type_error"


let pp_dfy_typ fmt t =
  fprintf fmt "%s" (string_of_dt t)

let rec dfy_type_of_symb_type : symbolic_type -> type_simple dafny_basic_type =
  function
  | Integer -> Int
  | Num -> Real
  | Real -> Real
  | Boolean -> Bool
  | _ -> Bottom

let pp_converted_stype fmt stype =
  pp_dfy_typ fmt (dfy_type_of_symb_type stype)
(* Conf variables :
   - Suffix for the Join : dafny_join_suffix
   - Prefix for the homorphism : dafny_hom_prefix
   - Assertion for empty list in homomorphism: dafny_hom_empty_assert
*)
let hom_prefix = Conf.get_conf_string "dafny_hom_prefix"
let join_suffix = Conf.get_conf_string "dafny_join_suffix"

let filename_of_solution sol = String.capitalize sol.loop_name

type proofVariable =
  {
    name : string;
    in_type : symbolic_type;
    out_type : symbolic_type;
    empty_value : skExpr;
    function_expr : skExpr;
    join_expr : skExpr;
    mutable base_case : int;
    mutable inspected : bool;
    mutable requires :
      ((Format.formatter -> (string * string)-> unit) * int) list;
    mutable depends : proofVariable list;
    mutable join_depends : proofVariable list;
  }

let vi_to_proofVars = IH.create 10
let input_seq_vi = ref None

let clear () =
  input_seq_vi := None;
  IH.clear vi_to_proofVars

let pp_dfy fmt (s, e, for_join) =
  (** Simple solution to go from the variables to
      functions of sequences : replace the variable
      names *)
  let replace_varnames expr =
    transform_expr
      (fun e -> false)
      identity (* Do not transform expressions *)
      identity (* Do not transform constants *)
      (* Transform only variables *)
      (fun v ->
         match v with
         | SkVarinfo vi ->
           let pfv = IH.find vi_to_proofVars vi.vid in
           if for_join then
             let _, _, is_from_right_state = is_right_state_varname vi.vname in
             if is_from_right_state then
               SkVarinfo {vi with vname = "right"^pfv.name}
             else
               SkVarinfo {vi with vname = "left"^pfv.name}
           else
             (** Replace by a recursive call *)
             let seq_arg =
               fprintf str_formatter "%s(%s[..|%s|-1])" pfv.name s s;
               flush_str_formatter ()
             in
             SkVarinfo {vi with vname = seq_arg}

         | SkArray (v, e) ->
           let input_i = check_option (vi_of v) in
           (** Check the index, two cases:
               - it is the current index.
               - it is the beggining of the chunk. *)
           begin
             match e with
             | SkVar (SkVarinfo i_vi) when is_left_index_vi i_vi ->
               SkVarinfo {input_i with vname = "s[0]"}
             | SkVar (SkVarinfo i_vi) ->
               SkVarinfo {input_i with vname = "s[|s|-1]"}
             | _ -> failwith "Cannot generate proofs whith complex indexes."
           end
         | _ -> failwith "Cannot generate proofs for tuples")
      expr
  in
  (pp_c_expr ~for_dafny:true) fmt (replace_varnames e)
(** Print the function corresponding to one variable. *)

let pp_function_body fmt (pfv, s) =
  fprintf fmt "@[<hv 2> if %s == [] then@; %a@;\
               else @;%a@;@]"
    s (pp_c_expr ~for_dafny:true) pfv.empty_value
    pp_dfy (s, pfv.function_expr, false)

let pp_function fmt (pfv, s) =
  fprintf fmt "@[function %s(%s: seq<%a>): %a@]@\n@[<v 2>{%a@]@\n}@\n@\n"
    pfv.name s pp_converted_stype pfv.in_type pp_converted_stype pfv.out_type
    pp_function_body (pfv, s)


(** Print the join corresponding to a variable.*)

let pp_join fmt pfv =
  let pp_args fmt thread =
    pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ", ")
      (fun fmt pfv -> fprintf fmt "%s%s : %a"
          thread pfv.name pp_converted_stype pfv.out_type)
      fmt
      pfv.join_depends
  in
  fprintf fmt "@[function %s%s(%a, %a): %a@]@\n@[<v 2>{@\n%a@]@\n}@\n@\n"
    pfv.name join_suffix pp_args "left" pp_args "right" pp_converted_stype pfv.out_type
    pp_dfy ("", pfv.join_expr, true)

(** Print the lemma ensuring we have an homomorphism *)
(* Require clauses *)

let pp_require_min_length i fmt sl =
  fprintf fmt "requires %a"
    (pp_print_list
       ~pp_sep:(fun fmt () -> fprintf fmt " && ")
       (fun fmt (seq_name, i) -> fprintf fmt "|%s| >= %i" seq_name i)) sl

let pp_requires fmt (s,t, reqs) =
  if reqs = [] then ()
  else
    pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "@\n")
      (fun fmt (p, _) -> p fmt (s, t)) fmt reqs

(* Assertions *)
let pp_assertion_emptylist fmt (s, t) =
  (* assert(s + [] == s); *)
  fprintf fmt "@[assert(%s + [] == %s);@]" s s


let pp_assertion_concat fmt (s,t) =
  (* {assert (s + t[..|t|-1]) + [t[|t|-1]] == s + t;} *)
  fprintf fmt "@[assert(%s + %s[..|%s|-1]) + [%s[|%s|-1]] == %s + %s;@]"
    s t t t t s t

let pp_func_of_concat fmt (pfv, s, t) =
  fprintf fmt "%s(%s + %s)" pfv.name s t


let pp_joined_res fmt (pfv, s, t) =
  let print_args fmt seqname =
    pp_print_list
      ~pp_sep:(fun fmt () -> fprintf fmt ", ")
      (fun fmt pfv -> fprintf fmt "%s(%s)" pfv.name seqname)
      fmt
      pfv.join_depends
  in
  fprintf fmt "%s(%a, %a)"
    (pfv.name^join_suffix)
    print_args s print_args t

let pp_depend_lemmas fmt (pfv, s, t) =
  pp_print_list
    ~pp_sep:(fun fmt () -> fprintf fmt "")
    (fun fmt dep_pfv -> fprintf fmt "%s%s(%s, %s[..|%s| - 1]);@;"
        hom_prefix dep_pfv.name s t t)
    fmt
    (List.filter (fun dep_pfv -> dep_pfv != pfv) pfv.join_depends)

let pp_hom fmt pfv s t =
  fprintf fmt "@\n\
               @[<v 2>lemma %s%s(%s : seq<%a>, %s : seq<%a>)@\n\
               @[%a@]
               @[ensures %a == %a@]@\n\
               @[<v 2>{@\n\
               if %s == [] @;{@;%a@\n\
               } else {@;\
               calc{@\n%a;@\n\
               @[<hv 2>=={@;%a%a@;}@]@\n%a;\
               @\n} // End calc.\
               @]@\n} // End else.\
               @]@\n} // End lemma.\
               @\n"
    hom_prefix pfv.name s pp_converted_stype pfv.in_type t
    pp_converted_stype pfv.in_type
    pp_requires (s, t, pfv.requires)
    pp_func_of_concat (pfv, s, t) pp_joined_res (pfv, s, t)
    t pp_assertion_emptylist (s,t)
    pp_func_of_concat (pfv, s, t)
    (* Use hommorphisms lemmas + default assertion *)
    pp_depend_lemmas (pfv, s, t) pp_assertion_concat (s,t)
    pp_joined_res (pfv, s, t)




(** TODO : substitutions when another state-variable on which
    the expression of the vi we are searching depends is bound
    before vi is bound *)
let find_exprs vi solved_sketch =
  let rec ret_binding vi ve_list =
    match ve_list with
    | (v, e)::tl ->
      if v = SkVarinfo vi then Some e else (ret_binding vi tl)
    | [] -> None
  in
  let rec find_binding vi sklet =
    match sklet with
    | SkLetIn (ve_list, letin) ->
      (match ret_binding vi ve_list with
       | Some e -> Some e
       | None -> find_binding vi letin)
    | SkLetExpr ve_list ->
      ret_binding vi ve_list
  in
  check_option (find_binding vi (sk_for_c solved_sketch.loop_body)),
  check_option (find_binding vi (sk_for_c solved_sketch.join_solution))

(**
   Rebuild max/min for a nicer syntax, but then we need to
    introduce the fitting definitions.
   Also replace the uses of min_int and max_int with the
   functions defined on sequences.
*)
let use_min = ref false
let use_max = ref false
let use_min_int = ref false
let use_max_int = ref false
let maxdef_avail = ref false
let mindef_avail = ref false

let clear_uses () =
  _boff use_min;
  _boff use_max;
  _boff use_min_int;
  _boff use_max_int;
  _boff maxdef_avail;
  _boff mindef_avail


let rebuild_min_max =
  let filter =
    function
    | SkQuestion (SkBinop (op, e1, e2), e1', e2')
      when e1 = e1' && e2 = e2' && (op = Lt || op = Gt) -> true
    | _ -> false
  in
  let transform rfunc e =
    match e with
    | SkQuestion (SkBinop (op, e1, e2), e1', e2')
      when e1 = e1' && e2 = e2' && (op = Lt || op = Gt) ->
      let e1o = rfunc e1 in
      let e2o = rfunc e2 in
      if op = Lt then
        (use_min := true; SkBinop (Min, e1o, e2o))
      else
        (use_max := true; SkBinop (Max, e1o, e2o))
    | _ -> e
  in
  transform_expr filter transform identity identity


(* Returns true if any of the max_int or min_int constants
   are used. *)
let rec uses_const lim  =
  rec_expr2
    {
      join = (fun u1 u2 -> u1 || u2);
      init = false;
      case = (fun e -> false);
      on_case = identity;
      on_const =
        (fun c ->
           match c with
           | c when c = lim -> true
           | _ -> false);
      on_var = (fun v -> false);
    }

let set_int_limit_uses e =
  if uses_const Infnty e then _bon use_max_int;
  if uses_const NInfnty e then  _bon use_min_int


(** Pretty print definitions. The name of the functions are set using
    the Conf module. *)
let pp_min_def fmt =
  _bon mindef_avail;
  fprintf fmt "function %s(x: int, y: int): int { if x > y then y else x}@.@."
    (Conf.get_conf_string "dafny_min_fun")


let pp_max_def fmt =
  _bon maxdef_avail;
  fprintf fmt "function %s(x: int, y: int): int { if x > y then x else y}@.@."
    (Conf.get_conf_string "dafny_max_fun")

let pp_max_int_def fmt =
  maxdef_avail -? pp_max_def fmt;
  fprintf fmt "@[<v 2>function %s(s : seq<int>) : int @\n\
               requires |s| >= 1@]@."
    (Conf.get_conf_string "dafny_max_seq_fun");
  fprintf fmt "@[<v 2>{@\n\
               if |s| == 1 then s[0]@;else@;%s(%s(s[..|s|-1]), s[|s|-1])@]\
               }"
    (Conf.get_conf_string "dafny_max_fun")
    (Conf.get_conf_string "dafny_max_seq_fun")

let pp_min_int_def fmt =
  mindef_avail -? pp_min_def fmt;
  fprintf fmt "@[<v 2>function %s(s : seq<int>) : int @\n\
               requires |s| >= 1@]@."
    (Conf.get_conf_string "dafny_min_seq_fun");
  fprintf fmt "@[<v 2>{@\n\
               if |s| == 1 then s[0]@;else@;%s(%s(s[..|s|-1]), s[|s|-1])@]\
               }"
    (Conf.get_conf_string "dafny_min_fun")
    (Conf.get_conf_string "dafny_min_seq_fun")

(**
   Generate the proof variables : one proof variable per state variables, and
    for each proof variable we will print a function, a join and the proof that
    the restriction is an homorphism
*)
let gen_proof_vars sketch =
  clear_uses ();
  let array_of_sketch =
    let arrays =
      VS.filter
        (fun vi -> CilTools.is_like_array vi)
        sketch.scontext.all_vars
    in
    if VS.cardinal arrays > 1 then
      failwith "Cannot generate proofs for multiple arrays."
    else
      VS.max_elt arrays
  in
  let special_req vi =
    if SketchJoin.is_left_aux vi.vid || SketchJoin.is_right_aux vi.vid then
      [pp_require_min_length 1, vi.vid]
    else []
  in
  let pfv_id = ref 0 in
  input_seq_vi := Some array_of_sketch;
  (* Fill the hash table *)
  VS.iter
    (fun vi ->
       let function_expr, join_expr = find_exprs vi sketch in
       let join_expr = rebuild_min_max join_expr in
       set_int_limit_uses function_expr;
       set_int_limit_uses join_expr;
       set_int_limit_uses (get_init_value sketch vi);
       let pfv_name = String.capitalize vi.vname in
       let pfv_base_case =
         if uses_const NInfnty function_expr ||
            uses_const Infnty function_expr
         then 1 else 0
       in
       incr pfv_id;
       IH.add vi_to_proofVars vi.vid
         {
           inspected = false;
           name = pfv_name;
           in_type = array_type (type_of_var (SkVarinfo array_of_sketch));
           out_type = type_of function_expr;
           base_case = pfv_base_case;
           empty_value = get_init_value sketch vi;
           function_expr = rebuild_min_max function_expr;
           requires = special_req vi;
           join_expr = join_expr;
           join_depends = [];
           depends = [];
         }
    )
    sketch.scontext.state_vars;
  (* Now the hash table contains the proof variables, we can compute
     the dependencies.
     We also need to update requirements accordingly.
  *)
  IH.iter
    (fun vid pfv ->
       let depend_set =
         VS.fold
           (fun vi dep_list ->
              (IH.find vi_to_proofVars vi.vid)::dep_list)
           (VS.inter sketch.scontext.state_vars
              (used_in_skexpr pfv.function_expr))
           []
       in
       let join_depend_set =
         VS.fold
           (fun vi dep_list ->
              (IH.find vi_to_proofVars vi.vid)::dep_list)
           (VS.inter sketch.scontext.state_vars
              (used_in_skexpr pfv.join_expr))
           []
       in
       let update_requires depend_set =
         (* Add requires clauses due to dependencies. *)
           List.fold_left
             (fun new_reqs pfv_dep -> new_reqs@pfv_dep.requires)
             pfv.requires depend_set
       in
       pfv.requires <- update_requires depend_set;
       pfv.depends <- depend_set;
       pfv.join_depends <- join_depend_set;) vi_to_proofVars


let pp_all_and_clear fmt =
  let s = "s" in let t = "t" in
  if !use_max then pp_max_def fmt;
  if !use_min then pp_min_def fmt;
  if !use_max_int then pp_max_int_def fmt;
  if !use_min_int then pp_min_int_def fmt;
  IH.iter (fun vid pfv -> pp_function fmt (pfv,s)) vi_to_proofVars;
  IH.iter (fun vid pfv -> pp_join fmt pfv) vi_to_proofVars;
  IH.iter (fun vid pfv -> pp_hom fmt pfv s t) vi_to_proofVars;
  clear_uses ();
  clear ()

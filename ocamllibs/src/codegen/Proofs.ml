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
  match stype with
  | Vector (t, _) ->
    pp_dfy_typ fmt (Sequence (dfy_type_of_symb_type t))
  | _ ->
    pp_dfy_typ fmt (dfy_type_of_symb_type stype)

let pp_input_params fmt varinfo_list =
  pp_print_list
    ~pp_sep:(fun fmt () -> fprintf fmt ",@;")
    (fun fmt vi -> fprintf fmt "%s : %a"
        vi.vname pp_converted_stype
        (type_of_ciltyp vi.vtype))
    fmt
    varinfo_list

let right_state_input_prefix = (Conf.get_conf_string "dafny_right_prefix")
let _R_ s = right_state_input_prefix^s

let pp_input_params_prefix fmt varinfo_list =
  pp_print_list
    ~pp_sep:(fun fmt () -> fprintf fmt ",@;")
    (fun fmt vi -> fprintf fmt "%s%s : %a"
        right_state_input_prefix
        vi.vname pp_converted_stype
        (type_of_ciltyp vi.vtype))
    fmt
    varinfo_list


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
    pid : int;
    name : string;
    sequence : varinfo;
    ivars : VS.t;
    in_vars : varinfo list;
    out_type : symbolic_type;
    empty_value : skExpr;
    function_expr : skExpr;
    join_expr : skExpr;
    mutable needs_base_case : bool;
    mutable pos_var : proofVariable option;
    mutable base_case : int;
    mutable inspected : bool;
    mutable func_requires : int;
    mutable func_requires_for_deps : int;
    mutable hom_requires : int * int;
    mutable depends : proofVariable list;
    mutable join_depends : proofVariable list;
  }

let vi_to_proofVars = IH.create 10
let input_seq_vi = ref None
let in_order = ref []

let clear () =
  input_seq_vi := None;
  IH.clear vi_to_proofVars;
  in_order := []


let pp_dfy fmt
    ((parent_pfv : proofVariable), (* The proofvariable we are printing for *)
     (ivars : VS.t), (* The set of index variables *)
     (seq : string), (* The name of the current sequence *)
     (e : skExpr), (* The expression to print *)
     (for_join : bool), (* Are we printing an expression for the join ? *)
     (r : bool)) =
  (** Simple solution to go from the variables to
      functions of sequences : replace the variable
      names *)
  let replace_varnames expr =
    transform_expr2
      { case = (fun e -> false);
        on_case = identity; (* Do not transform expressions *)
        on_const = identity; (* Do not transform constants *)
        on_var = (* Transform only variables *)
          (fun v ->
             match v with
             | SkVarinfo vi ->
               begin
                 try
                   let pfv =
                     IH.find vi_to_proofVars vi.vid
                   in
                   if for_join then
                     let _, _, is_from_right_state = is_right_state_varname vi.vname in
                     if is_from_right_state then
                       SkVarinfo {vi with vname = "right"^pfv.name}
                     else
                       SkVarinfo {vi with vname = "left"^pfv.name}
                   else
                     (** Replace by a recursive call *)
                     let seq_arg =
                       fprintf str_formatter "%s(%s[..|%s|-1])" pfv.name seq seq;
                       flush_str_formatter ()
                     in
                     SkVarinfo {vi with vname = seq_arg}
                 with Not_found ->
                   (if r
                    then SkVarinfo
                        {vi with vname = right_state_input_prefix^vi.vname}
                    else
                      (if VS.mem vi ivars then
                         let name = (Conf.get_conf_string "dafny_length_fun")^
                                    "("^seq^")" in
                         SkVarinfo {vi with vname = name}
                       else v))
               end

             | SkArray (v, e) ->
               let input_i = check_option (vi_of v) in
               (** Check the index, two cases:
                   - it is the current index.
                   - it is the beggining of the chunk. *)
               begin
                 match e with
                 | SkVar (SkVarinfo i_vi) when is_left_index_vi i_vi ->
                   let name = seq^"[0]" in
                   SkVarinfo {input_i with vname = name}

                 | SkVar (SkVarinfo i_vi) ->
                   let name = seq^"[|"^seq^"|-1]" in
                   SkVarinfo {input_i with vname = name}

                 | _ -> failwith "Cannot generate proofs whith complex indexes."
               end
             | _ -> failwith "Cannot generate proofs for tuples");}
      expr
  in
  let add_pos_offset e =
    if is_some parent_pfv.pos_var then
      let var_with_offset cur_pfv vi =
        let pos_var = check_option cur_pfv.pos_var in
        if str_begins_with "right" vi.vname then
          SkBinop
            (Plus, SkVar (SkVarinfo vi),
             SkVar (SkVarinfo {vi with
                               vname = "left"^pos_var.name}))
        else
          SkVar (SkVarinfo vi)
      in
      let transf =
        { case =
            (fun e -> match e with SkVar (SkVarinfo vi) -> true | _ -> false);
          on_case =
            (fun f e ->
               match e with
               | SkVar (SkVarinfo vi) ->
                 begin
                   try
                     let pfv =
                       IH.find vi_to_proofVars vi.vid
                     in
                     if is_some pfv.pos_var then
                       var_with_offset pfv vi
                     else
                       e
                   with Not_found -> e
                 end
               | _ -> e);
          on_const = identity;
          on_var = identity;
        }
      in
      transform_expr2 transf e
    else e
  in
  (pp_c_expr ~for_dafny:true) fmt (add_pos_offset (replace_varnames e))
(** Print the function corresponding to one variable. *)

let pp_base_case_cond fmt pfv =
  if pfv.base_case = 0 then
    fprintf fmt "%s == []" (_R_ pfv.sequence.vname)
  else
    fprintf fmt "|%s| == %i" (_R_ pfv.sequence.vname)
      pfv.base_case

let pp_func_base_case_cond fmt pfv =
  if pfv.func_requires_for_deps <= 0 then
    fprintf fmt "%s == []" pfv.sequence.vname
  else
    fprintf fmt "|%s| == %i" pfv.sequence.vname pfv.func_requires_for_deps

let pp_requires_fun fmt pfv =
  if pfv.func_requires_for_deps > 0 then
    fprintf fmt "@\nrequires |%s| >= %i"
      pfv.sequence.vname pfv.func_requires_for_deps

let pp_init_value fmt pfv =
  if pfv.func_requires = 1 then
    fprintf fmt "%s[0]" pfv.sequence.vname
  else
    (pp_c_expr ~for_dafny:true fmt pfv.empty_value)

let pp_function_body fmt pfv =
  fprintf fmt "@[<hv 2>if %a then@;%a@;\
               else@;%a@]"
    pp_func_base_case_cond pfv
    pp_init_value pfv
    pp_dfy (pfv, pfv.ivars, pfv.sequence.vname , pfv.function_expr, false, false)

let pp_function fmt pfv =
  fprintf fmt "@[function %s(%a): %a@]%a@\n@[<v 2>{@\n%a@]@\n}@\n@\n"
    pfv.name pp_input_params pfv.in_vars pp_converted_stype pfv.out_type
    (* Some function might need require statements *)
    pp_requires_fun pfv
    pp_function_body pfv


(** Print the join corresponding to a variable.*)
let get_join_args pfv =
  pfv.join_depends@(match pfv.pos_var with Some x -> [x] | None -> [])

let pp_join fmt pfv =
  (* Arguments of the join : the variables the join depends on and
     if needed we need to add the length of the sequences (for state
     variables that depend on the position) *)
  let pp_args fmt thread =
    pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ", ")
      (fun fmt pfv -> fprintf fmt "%s%s : %a"
          thread pfv.name pp_converted_stype pfv.out_type)
      fmt
      (get_join_args pfv)
  in
  fprintf fmt "@[function %s%s(%a, %a): %a@]@\n@[<v 2>{@\n%a@]@\n}@\n@\n"
    pfv.name join_suffix pp_args "left" pp_args "right"
    pp_converted_stype pfv.out_type
    pp_dfy (pfv, pfv.ivars, "", pfv.join_expr, true, true)

(** Print the lemma ensuring we have an homomorphism *)
(* Require clauses *)

let pp_require_min_length fmt sl =
  fprintf fmt "requires %a@\n"
    (pp_print_list
       ~pp_sep:(fun fmt () -> fprintf fmt " && ")
       (fun fmt (seq_name, i) -> fprintf fmt "|%s| >= %i" seq_name i)) sl

let pp_requires fmt pfv =
  match pfv.hom_requires with
  | (0, 0) -> ()
  | (l, r) ->
    fprintf fmt "requires |%s| >= %i && |%s| >= %i@\n"
      pfv.sequence.vname l (_R_ pfv.sequence.vname) r

let pp_requires_basecase fmt pfv =
  match pfv.hom_requires with
  | (0, 0) -> ()
  | (l, r) ->
    if pfv.func_requires_for_deps >= 1 then
      fprintf fmt "requires |%s| >= %i && |%s| >= %i@\n"
        pfv.sequence.vname l (_R_ pfv.sequence.vname) r
    else
      fprintf fmt "requires |%s| >= %i@\n"
        pfv.sequence.vname l

(* Assertions *)
let pp_assertion_base_case fmt pfv =
  (* assert(s + [] == s); *)
  if pfv.func_requires_for_deps = 0 then
    fprintf fmt "@[assert(%s + [] == %s);@]"
      pfv.sequence.vname pfv.sequence.vname
  else
    begin
      if pfv.func_requires_for_deps = 1 then
        fprintf fmt "@[assert(%s + %s == %s + [%s[0]]);@]"
          pfv.sequence.vname
          (_R_ pfv.sequence.vname)
          pfv.sequence.vname
          (_R_ pfv.sequence.vname)
      else
        fprintf fmt "@[assert(%s + %s == %s + %s[..%i]);@]"
          pfv.sequence.vname
          (_R_ pfv.sequence.vname)
          pfv.sequence.vname
          (_R_ pfv.sequence.vname)
          pfv.base_case
    end


let pp_assertion_concat fmt pfv =
  let s = pfv.sequence.vname in let t = _R_ pfv.sequence.vname in
  (* {assert (s + t[..|t|-1]) + [t[|t|-1]] == s + t;} *)
  fprintf fmt "@[assert(%s + %s[..|%s|-1]) + [%s[|%s|-1]] == %s + %s;@]"
    s t t t t s t

let pp_func_of_concat fmt pfv =
  fprintf fmt "%s(%s + %s)" pfv.name pfv.sequence.vname (_R_ pfv.sequence.vname)

let pp_func_of_concat_base_case fmt pfv =
  fprintf fmt "%s(%s + %a)" pfv.name pfv.sequence.vname
    (fun fmt pfv ->
       if pfv.func_requires_for_deps = 1 then
         fprintf fmt "[%s[0]]" (_R_ pfv.sequence.vname)
       else
         fprintf fmt "%s[..%i]" (_R_ pfv.sequence.vname)
           pfv.func_requires_for_deps) pfv

let pp_func_of_single_list fmt pfv =
  fprintf fmt "%s(%s)" pfv.name pfv.sequence.vname

let pp_joined_res fmt pfv =
  let print_args fmt seqname =
    pp_print_list
      ~pp_sep:(fun fmt () -> fprintf fmt ", ")
      (fun fmt pfv -> fprintf fmt "%s(%s)" pfv.name seqname)
      fmt
      (get_join_args pfv)
  in
  fprintf fmt "%s(%a, %a)"
    (pfv.name^join_suffix)
    print_args pfv.sequence.vname
    print_args (right_state_input_prefix^pfv.sequence.vname)

let pp_joined_base_case fmt pfv =
  let print_args fmt seqname =
    pp_print_list
      ~pp_sep:(fun fmt () -> fprintf fmt ", ")
      (fun fmt pfv -> fprintf fmt "%s(%s)" pfv.name seqname)
      fmt
      (get_join_args pfv)
  in
  let print_inits fmt s =
    pp_print_list
      ~pp_sep:(fun fmt () -> fprintf fmt ", ")
      (fun fmt pfv_ ->
         fprintf fmt "%s(%s)" pfv_.name
           (if pfv.base_case = 0 then "[]"
            else
              (if pfv.base_case = 1
               then
                 "["^(_R_ pfv.sequence.vname)^"[0]]"
               else
                 (_R_ pfv.sequence.vname)^"[.."^
                 (string_of_int pfv.base_case)^"]")))
      fmt
      (get_join_args pfv)
  in
  fprintf fmt "%s(%a, %a)"
    (pfv.name^join_suffix)
    print_args pfv.sequence.vname print_inits pfv.sequence.vname


let pp_depend_lemmas fmt pfv =
  let s = pfv.sequence.vname in let t = _R_ pfv.sequence.vname in
  pp_print_list
    ~pp_sep:(fun fmt () -> fprintf fmt "")
    (fun fmt dep_pfv -> fprintf fmt "%s%s(%s, %s[..|%s| - 1]);@;"
        hom_prefix dep_pfv.name s t t)
    fmt
    (List.filter (fun dep_pfv -> dep_pfv != pfv) (get_join_args pfv))

let pp_base_case_cond fmt pfv =
  if pfv.func_requires_for_deps = 0 then
    fprintf fmt "%s == []" (_R_ pfv.sequence.vname)
  else
    fprintf fmt "|%s| == %i" (_R_ pfv.sequence.vname)
      pfv.func_requires_for_deps

let pp_hom fmt pfv =
  (** Print the base case lemma *)
  (if pfv.needs_base_case then
     fprintf fmt
       "@\n\
        @[<v 2>lemma BaseCase%s(%a)@\n\
        %a\
        ensures %a == %a@\n\
        {}@."
       pfv.name
       (fun fmt pfv ->
          if pfv.base_case = 0 then
            pp_input_params fmt pfv.in_vars
          else
            fprintf fmt "%a, %a"
              pp_input_params pfv.in_vars
              pp_input_params_prefix pfv.in_vars) pfv
       pp_requires_basecase pfv
       (if let l,r = pfv.hom_requires in l <= 0 && r <= 0
        then pp_func_of_single_list
        else pp_func_of_concat_base_case) pfv
       pp_joined_base_case pfv);
  (* Print the main lemma *)
  fprintf fmt
    "@\n\
     @[<v 2>lemma %s%s(%a, %a)@\n\
     @[%a@]\
     @[ensures %a == %a@]@\n\
     @[<v 2>{@\n\
     if %a @;{@;%a@\n\
     %a
     } else {@;\
     calc{@\n%a;@\n\
     @[<hv 2>=={@;%a%a@;}@]@\n%a;\
     @\n} // End calc.\
     @]@\n} // End else.\
     @]@\n} // End lemma.\
     @\n"
    hom_prefix pfv.name  pp_input_params pfv.in_vars
    pp_input_params_prefix pfv.in_vars
    (* Might requires some hypothesis if the function is undefined for small
       sequences *)
    pp_requires pfv
    (* Ensures function of concatenated lists equals the results of the join *)
    pp_func_of_concat pfv pp_joined_res pfv
    pp_base_case_cond pfv
    pp_assertion_base_case pfv
    (fun fmt pfv ->
       if pfv.needs_base_case then
         fprintf fmt "BaseCase%s(%a);@\n"
           pfv.name
           (fun fmt pfv ->
              if pfv.base_case = 0
              then
                fprintf fmt "%s" pfv.sequence.vname
              else
                fprintf fmt "%s, %s"
                  pfv.sequence.vname
                  (_R_ pfv.sequence.vname)) pfv) pfv
    pp_func_of_concat pfv
    (* Use hommorphisms lemmas + default assertion *)
    pp_depend_lemmas pfv pp_assertion_concat pfv
    pp_joined_res pfv



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
  let flat_function =
    force_flat solved_sketch.scontext.state_vars solved_sketch.loop_body
  in
  (try
     check_option (find_binding vi flat_function)
   with Failure s -> failwith "Failed to find expressions."),
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
let need_hom_length = ref false
let length_hom_printed = ref false

let clear_uses () =
  _boff use_min;
  _boff use_max;
  _boff use_min_int;
  _boff use_max_int;
  _boff maxdef_avail;
  _boff mindef_avail;
  _boff need_hom_length;
  _boff length_hom_printed


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
           | c when List.mem c lim -> true
           | _ -> false);
      on_var = (fun v -> false);
    }

let set_int_limit_uses e =
  if uses_const [Infnty] e then _bon use_max_int;
  if uses_const [NInfnty] e then  _bon use_min_int


(** Pretty print definitions. The name of the functions are set using
    the Conf module. *)
let pp_length_def fmt () =
  fprintf fmt
    "function %s(s: seq<int>): int@\n\
     {if s == [] then 0 else %s(s[..|s|-1]) + 1}@.@."
    (Conf.get_conf_string "dafny_length_fun")
    (Conf.get_conf_string "dafny_length_fun")

let pp_hom_length fmt () =
  if !length_hom_printed then ()
  else
    begin
      _bon length_hom_printed;
      let fname = (Conf.get_conf_string "dafny_length_fun") in
      fprintf fmt
        "function %sJoin(a: int, b: int): int@\n\
         { a + b }@." fname;
      fprintf fmt
        "lemma Hom%s(s: seq<int>, t: seq<int>)@\n\
         ensures %s(s + t) == %sJoin(%s(s), %s(t))@\n\
         @[<v 2>{@\n\
	 if t == [] {@\n\
	 assert(s + t == s);@]@\n\
	 } else @[<v 1>{@\n\
	 calc {@\n\
	 %s(s + t);@\n\
	 == {assert (s + t[..|t|-1]) + [t[|t|-1]] == s + t;}@\n\
         %sJoin(%s(s), %s(t));@\n\
	 }@\n\
	 }@]@\n\
         }@\n@."
        fname fname fname fname fname fname fname fname fname
    end

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
               if |s| == 1 then s[0]@;else@;%s(%s(s[..|s|-1]), s[|s|-1])@]@\n\
               }@."
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
      try
        VS.max_elt arrays
      with Not_found ->
        (makeVarinfo false (Conf.get_conf_string "dafny_seq_placeholder")
           (TArray ((TInt ((IInt), []), None, []))))
  in
  (* Create a proofVariable for the index, that will be used in state variables
     that depend on position *)
  let index_pfv =
    let v, (i, g, u) = sketch.sketch_igu in
    let index_vi = VS.min_elt sketch.scontext.index_vars in
    let index_name = Conf.get_conf_string "dafny_length_fun" in
    {
      pid = index_vi.vid;
      inspected = false;
      name = index_name;
      sequence = array_of_sketch;
      ivars = VS.empty;
      in_vars =  [];
      pos_var = None;
      out_type = Integer;
      base_case = 0;
      needs_base_case = false;
      empty_value = SkConst (CInt 0);
      function_expr = g;
      func_requires = 0;
      func_requires_for_deps = 0;
      hom_requires = (0,0);
      join_expr = g;
      join_depends = [];
      depends = [];
    }
  in
  (** Each proofVariable has its own Id different from the vi's id *)
  let pfv_id = ref 0 in
  input_seq_vi := Some array_of_sketch;
  (* Fill the hash table *)
  VS.iter
    (fun vi ->
       let function_expr, join_expr = find_exprs vi sketch in
       (* Identify the variables used by the function that are not
          state variables. In most cases this will only be the input
          sequence *)
       let in_vars =
         VS.filter
           (fun vi -> not (is_left_index_vi vi || is_right_index_vi vi))
           (VS.diff (used_in_skexpr function_expr)
              (VS.union sketch.scontext.state_vars
                 sketch.scontext.index_vars))
       in
       let input_vars =
         if VS.cardinal in_vars >= 1 then
           VSOps.varlist in_vars else
           [array_of_sketch]
       in
       (* Replace ternary expressions that correspond to a min/max *)
       let join_expr = rebuild_min_max join_expr in
       set_int_limit_uses function_expr;
       set_int_limit_uses join_expr;
       set_int_limit_uses (get_init_value sketch vi);
       let pfv_name = String.capitalize vi.vname in
       (* In some cases, a function needs to be defined only on sequences
          with a length > minimal length *)
       let init_va = get_init_value sketch vi in
       let pfv_elim_non_empty =
         if (SketchJoin.is_left_aux vi.vid
             || SketchJoin.is_right_aux vi.vid
             || uses_const [NInfnty; Infnty] function_expr
             || uses_const [NInfnty; Infnty] init_va)
         then 1 else 0
       in
       (* If the function uses the position (length) then we
          might need to add the length homorphism lemma *)
       let uses_pos =
         let recursor = {
           join = (fun a b -> a || b);
           init = false;
           case = (fun e -> match e with SkQuestion _ -> true | _ -> false);
           on_case =
             (fun f e ->
                match e with
                | SkQuestion (c, e1, e2) -> f e1 || f e2
                | _ -> false);
           on_const = (fun c -> false);
           on_var =
             (fun v ->
                match v with
                | SkVarinfo vi when VS.mem vi sketch.scontext.index_vars -> true
                | _ -> false)
         } in
         rec_expr2 recursor function_expr
       in
       if uses_pos then _bon need_hom_length;
       incr pfv_id;
       IH.add vi_to_proofVars vi.vid
         {
           pid = vi.vid;
           inspected = false;
           name = pfv_name;
           sequence = array_of_sketch;
           ivars = sketch.scontext.index_vars;
           in_vars =  input_vars;
           pos_var = if uses_pos then Some index_pfv else None;
           out_type = type_of function_expr;
           base_case = pfv_elim_non_empty;
           needs_base_case = false;
           empty_value = init_va;
           function_expr = rebuild_min_max function_expr;
           func_requires = pfv_elim_non_empty;
           func_requires_for_deps = 0;
           hom_requires = (0,0);
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
  let pfv_list = IHTools.key_list vi_to_proofVars in
  let update_deps_pfv vid pfv =
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
    pfv.depends <- depend_set;
    pfv.join_depends <- join_depend_set
  in

  (* Compute order according to dependencies *)
  let dep_order_list =
    List.fold_left
      (fun vi_list vid ->
         if List.mem vid vi_list then
           vi_list
         else
           let dep_set = (IH.find vi_to_proofVars vid).depends in
           let id_dep_set = List.map (fun pfv -> pfv.pid) dep_set in
           id_dep_set@[vid]@vi_list)
      []
      pfv_list
  in
  let update_requires_pfv vid pfv =
    let updated_hom_requires depend_set =
      List.iter
        (fun pfv_dep -> pfv_dep.needs_base_case <- true)
        pfv.depends;
      List.fold_left
        (fun (l, r) pfv_dep ->
           pfv.base_case <- max pfv.base_case pfv_dep.base_case;
           let l_dep, r_dep = pfv_dep.hom_requires in
           if l_dep > 0 || r_dep > 0 then
             (max l (l_dep + 1), max r (r_dep + 1))
           else (0, 0))
        pfv.hom_requires depend_set
    in
    let updated_func_requires_deps depend_set =
      List.fold_left
        (fun r pfv_dep ->
           let r_dep = pfv_dep.func_requires in
           if r_dep > 0 then max r r_dep else r)
        pfv.func_requires depend_set
    in
    pfv.func_requires_for_deps <- updated_func_requires_deps pfv.depends;
    (* Homorphism lemma requirements should at least meet the function's
       requirements in terms of input sequence length. *)
    pfv.hom_requires <- (let r, l = updated_hom_requires pfv.join_depends in
                         let fr = pfv.func_requires_for_deps in
                         (max r fr, max l fr))
  in
  List.iter
    (fun vid -> update_deps_pfv vid (IH.find vi_to_proofVars vid))
    pfv_list;
  List.iter
    (fun vid -> update_requires_pfv vid (IH.find vi_to_proofVars vid))
    dep_order_list;
  in_order := dep_order_list



let pp_all_and_clear fmt =
  pp_length_def fmt ();
  if !use_max then pp_max_def fmt;
  if !use_min then pp_min_def fmt;
  if !use_max_int then pp_max_int_def fmt;
  if !use_min_int then pp_min_int_def fmt;
  let iter_pfv (pfun: int -> proofVariable -> unit) =
    List.iter
      (fun vid -> pfun vid (IH.find vi_to_proofVars vid))
      !in_order
  in
  iter_pfv (fun vid pfv ->
      if is_some pfv.pos_var then pp_hom_length fmt ());
  (* Print all function *)
  iter_pfv (fun vid pfv -> pp_function fmt pfv);
  iter_pfv (fun vid pfv -> pp_join fmt pfv);
  iter_pfv (fun vid pfv -> pp_hom fmt pfv);
  clear_uses ();
  clear ()

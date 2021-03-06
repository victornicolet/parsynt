(**
   This file is part of Parsynt.

    Parsynt is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Parsynt is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Parsynt.  If not, see <http://www.gnu.org/licenses/>.
*)

open Format
open Cil

open Beta
open Fn
open FnPretty
open Utils
open Utils.PpTools

module Ct = CilTools

let class_member_appendix = Config.get_conf_string "class_member_appendix"

let convtype_of_v v =
  match ciltyp_of_symb_type v.vtype with
  | Some t -> t
  | None -> TVoid ([])

(** Class constructor argument *)
type cpp_include =
  | IncludeLocal of string
  | IncludeGlobal of string

let pp_include fmt includ =
  match includ with
  | IncludeLocal s -> fprintf fmt "#include \"%s.h\"@." s
  | IncludeGlobal s -> fprintf fmt "#include <%s>@." s

type cpp_constr_arg =
  | FormalArg of fnV
  | FormalRefArg of fnV
  | SpecialArg of string



let pp_cpp_constr_arg fmt =
  function
  | FormalArg vi ->
    fprintf fmt "%s %s"
      (Ct.psprint80 dn_type (convtype_of_v vi)) vi.vname
  | FormalRefArg vi ->
    fprintf fmt "%s& %s"
      (Ct.psprint80 dn_type (convtype_of_v vi)) vi.vname
  | SpecialArg s ->
    fprintf fmt "%s" s

let pp_constr_arg_in_app fmt =
  function
  | FormalArg vi
  | FormalRefArg vi ->
    fprintf fmt "%s" vi.vname
  | SpecialArg s ->
    fprintf fmt "%s" s

type cpp_constr_initializer = fnV * init_expr

and init_expr =
  | ConstExpr of fnExpr
  | ClassMember of fnV * string
  | LocalVar of fnV

let pp_initializer fmt (vi, init) =
  fprintf fmt "%s%s(%s)"
    class_member_appendix
    vi.vname
    (match init with
     | ConstExpr exp -> (fprintf str_formatter "%a"
                           (pp_c_expr ~for_dafny:false) exp;
                         flush_str_formatter ())
     | ClassMember (vi', s) -> s^"."^vi.vname
     | LocalVar vi' -> vi'.vname)

(** Class constructor *)
type cpp_class_constr =
  {
    cid : int;
    ctype : typ;
    cname : string;
    cargs : cpp_constr_arg list;
    cbody : stmt;
    cinitializers : cpp_constr_initializer list;
  }

let makeConstructor cn ct cid cargs cb cinit =
  { cid = cid; ctype = ct; cname = cn;
    cargs = cargs; cbody = cb; cinitializers = cinit;}

let pp_cpp_constructor fmt cpp_constructor =
  fprintf fmt "@[<hv 2>%s(%a):@;%a {@[<hov 2>%s@]}@]@\n"
    (* Constructor name *)
    cpp_constructor.cname
    (* Constructor arguments *)
    (fun f li -> ppli f ~sep:", " pp_cpp_constr_arg li)
    cpp_constructor.cargs
    (* Constructor initializers *)
    (fun f li -> ppli f ~sep:", " pp_initializer li)
    cpp_constructor.cinitializers
    (* Constructor body *)
    (Ct.psprint80 dn_stmt cpp_constructor.cbody)


(** Simplified methods : we don't use directly Cil's fundecs *)
type cpp_class_method =
  {
    mattributes : string list;
    mtyp : typ;
    mname : string;
    margs : cpp_constr_arg list;
    mid : int;
    mbody : stmt;
    mlocals : VarSet.t;
    mcpp : bool;
    mprint : (formatter -> unit -> unit) option;
  }


let pp_method fmt cmet =
  fprintf fmt "@[<hv 2>%s %s(%a)@;\
               {@;<1>@[<v>%a@\n%a@]@;}@]"
    (* The return type of the method *)
    (Ct.psprint80 dn_type cmet.mtyp)
    (* The name of the method *)
    cmet.mname
    (* Arguments, we reuse the cpp_constr_arg type *)
    (pp_print_list
       ~pp_sep:(fun fmt () ->  fprintf fmt ", ")
       pp_cpp_constr_arg) cmet.margs

    (* Print the local variables's declarations *)
    (fun fmt () ->
       (VarSet.iter
          (fun vi ->
             fprintf fmt "%s %s;@\n" (Ct.psprint80 dn_type (convtype_of_v vi)) vi.vname))
         cmet.mlocals)
    ()

    (* Print the body of the method :
       either a printer has been provided or we print the statements *)
    (fun fmt () ->
       match cmet.mprint with
       | Some printer -> printer fmt ()
       | None -> fprintf fmt "%s"
                   (Ct.psprint80 dn_stmt cmet.mbody))
    ()


(** Class type *)
type cpp_class =
  {
    cname : string;
    ctype : typ;
    mutable private_vars : VarSet.t;
    mutable public_vars : VarSet.t;
    mutable constructors : cpp_class_constr list;
    mutable public_members : cpp_class_method list
  }

let makeEmptyClass class_name =
  let class_type =
    TNamed ({tname = "class_name"; ttype = TVoid []; treferenced = true}, [])
  in
  {
    cname = class_name;
    ctype = class_type;
    private_vars = VarSet.empty;
    public_vars = VarSet.empty;
    constructors = [];
    public_members = [];
  }

let pp_class fmt cls =
  let pp_members fmt vs =
    VarSet.iter
      (fun vi -> fprintf fmt "@[%s %s%s;@]@;"
          (Ct.psprint80 Cil.dn_type (convtype_of_v vi)) class_member_appendix vi.vname)
      vs
  in
  let pp_class_body fmt cls =
    fprintf fmt "@[<v 2>\
                 private:@;%a@]@;\
                 @[<v 2>\
                 public:@;\
                 %a@\n@\n\
                 %a@\n@\n\
                 %a@]@;"
      pp_members cls.private_vars
      pp_members  cls.public_vars
      (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "@;")
         pp_cpp_constructor) cls.constructors
      (pp_print_list
         ~pp_sep:(fun fmt () -> fprintf fmt "@;")
         (fun fmt methode -> pp_method fmt methode))
      cls.public_members
  in
  fprintf fmt "@[<v>class %s {@;%a};@]"
    cls.cname
    pp_class_body cls

(** Specific use of the C++ class for our problem **)


let class_name_appendix = Config.get_conf_string "class_name_appendix"

let iterator_type_name = Config.get_conf_string "tbb_iterator_type_name"

let iterator_name = Config.get_conf_string "tbb_iterator_name"

(** The iterator has type long *)
let iterator_c_typ = TInt (ILong,[])

(**
   In the "operator()" definition, the _begin_ and _end_ indexes
    need to be renamed by appending the class_member_appendix prefix.
*)

let rec rename_bounds e =
  let rename_index_vi skv =
    match skv with
    | FnVariable vi ->
      begin
        if is_left_index_vi vi || is_right_index_vi vi then
          FnVariable {vi with vname = class_member_appendix^vi.vname}
        else
          FnVariable vi
      end
    | FnArray (v, e) -> FnArray (v, rename_bounds e)
  in
  transform_expr2
    { case = (fun e -> false);
      on_case = (fun f e -> e);
      on_const = (fun c -> c);
      on_var = rename_index_vi } e


(** In the loop body of the operator, some assignments might be repeptitive, due
    to the introduction of auxliiaries. Remove them from the body and return
    them in a separate list to be printed out of the loop. *)
let remove_constant_assignments sktch sklet =
  let is_constant_assignment v e =
    let used_vars = used_in_fnexpr e in
    (* The expression doesn't use state variables or an index *)
    VarSet.is_empty
      (VarSet.union
         (VarSet.inter sktch.scontext.state_vars used_vars)
         (VarSet.inter sktch.scontext.index_vars used_vars))
  in
  let rem_from_ve_list ve_list =
    List.fold_left
      (fun (ve_l, c_a) (v, e) ->
         if is_constant_assignment v e then ve_l, c_a@[(v,e)]
         else ve_l@[(v,e)], c_a)
      ([], [])
      ve_list
  in
  let rec aux sklet c_a =
    match sklet with
    | FnLetIn (ve_list, letin) ->
      let ve_list0, c_a0 = rem_from_ve_list ve_list in
      let letin0, c_a1 = aux letin (c_a@c_a0) in
      FnLetIn (ve_list0, letin0), c_a1
    | e -> e, c_a
  in
  aux sklet []


(* Print the includes, the namepace and the type declaration necessary
   before actually declaring the class representing the problem *)
let fprint_test_prelude fmt pb_header_filename =
  let includes = [IncludeGlobal "iostream"; IncludeGlobal "tbb/tbb.h";
                  IncludeLocal pb_header_filename] in
  pp_print_list
    ~pp_sep:(fun fmt () -> ())
    pp_include fmt includes;
  fprintf fmt "@.using namespace tbb;@.";
  fprintf fmt "@.typedef %s %s;@.@."
    (Ct.psprint80 dn_type iterator_c_typ) iterator_type_name

(** Generate different names or sets of variables needed in the
    class declaration *)
let pbname_of_sketch solution =
  (solution.host_function.fvar.vname ^ (string_of_int solution.id))

let private_vars_of_sketch sketch =
  VarSet.diff (VarSet.diff sketch.scontext.used_vars sketch.scontext.state_vars)
    sketch.scontext.index_vars

let pp_operator_body fmt pb (i, b, e) constant_assignments ppbody =
  let pp_c_a fmt c_as =
    if List.length c_as = 0 then ()
    else
      fprintf fmt "%a@\n" (pp_c_assignment_list false) c_as
  in
  (* Local versions of the class's variables *)
  VarSet.iter
    (fun vi ->
       fprintf fmt "%s %s = %s%s;@\n"
         (Ct.psprint80 dn_type (check_option (ciltyp_of_symb_type vi.vtype)))
         vi.vname
         class_member_appendix vi.vname)
    (VarSet.union pb.scontext.used_vars pb.scontext.state_vars);
  fprintf fmt "@\n";
  (* Index bounds must be prefixed by "my_" *)
  let b, e = {b with vname = class_member_appendix^b.vname},
             {e with vname = class_member_appendix^e.vname}
  in
  (* Bounds intialization *)
  fprintf fmt
    "@[<v>\
     @[if (%s < 0 || %s.begin() < %s)@]@\n\
     @[%s = r.begin();@;@]@\n\
     @[if (%s < 0 || %s.end() > %s)@]@\n\
     @[%s = r.end();@]@]@\n@\n"
    b.vname iterator_name b.vname b.vname
    e.vname iterator_name e.vname e.vname
  ;
  (* Constant assignments *)
  pp_c_a fmt constant_assignments;
  (* Main loop *)
  fprintf fmt
    "@[<hv 2>for (%s %s = %s.begin(); %s!= %s.end(); ++%s) {@;%a@;}@]@;"
    iterator_type_name i.vname iterator_name
    i.vname iterator_name
    i.vname
    ppbody ();
  (* Update class vars that need it *)
  VarSet.iter
    (fun vi ->
       fprintf fmt "@[%s%s = %s;@]@;" class_member_appendix vi.vname vi.vname)
    pb.scontext.state_vars


let make_tbb_class pb =
  let class_name =
    class_name_appendix^(String.capitalize (pbname_of_sketch pb))
  in
  let tbb_class = makeEmptyClass class_name in
  (* let index_type =
   *   TNamed (
   *     { tname = iterator_type_name;
   *       ttype = iterator_c_typ;
   *       treferenced = false;},[])
   * in *)
  let index_var = VarSet.max_elt pb.scontext.index_vars in
  let begin_index_var = left_index_vi index_var in
  let end_index_var = right_index_vi index_var in

  tbb_class.private_vars <- private_vars_of_sketch pb;
  tbb_class.public_vars <-
    VarSet.union pb.scontext.state_vars
      (VarSet.of_list [begin_index_var; end_index_var]);
  let bounds_initial_values =
    IM.add begin_index_var.vid
      (FnConst
         (CInt64 (Int64.of_string
                    (Config.get_conf_string "tbb_begin_index_value"))))
      (IM.add end_index_var.vid
         (FnConst
            (CInt64
               (Int64.of_string
                  (Config.get_conf_string "tbb_end_index_value")))) IM.empty)
  in
  let public_vars_inits =
    let maybe_inits =
      List.map
        (fun vi ->
           try vi, Some (get_init_value pb vi)
           with Not_found ->
           try vi, Some (IM.find vi.vid bounds_initial_values)
           with Not_found -> vi, None)
        (VarSet.elements tbb_class.public_vars)
    in
    List.map
      (fun (vi, maybe_init) ->
         match maybe_init with
         | Some init_expr -> vi, ConstExpr init_expr
         | None ->
           failwith (fprintf str_formatter
                       "No initiallization found for %s." vi.vname;
                     flush_str_formatter ()))
      maybe_inits
  in
  let tbb_cstr_copy =
    (** Copy constructor takes as argument an instance of the class,
        and a special argument split :

        Parallel<pb_name>(Parallel<pb_name>& <var>, split) {}
    *)
    let copy_from_name =
      (Config.get_conf_string "tbb_right_state_name")
    in
    let copy_cstr_args =
      [SpecialArg
         (class_name^"& "^copy_from_name);
       SpecialArg "split"]
    in
    let copy_cstr_initializers =
      let private_vars_inits =
        List.map (fun vi -> (vi, ClassMember (vi, copy_from_name)))
          (VarSet.elements tbb_class.private_vars)
      in
      private_vars_inits @ public_vars_inits
    in
    makeConstructor
      class_name
      tbb_class.ctype
      1
      copy_cstr_args
      (mkStmt (Instr []))
      copy_cstr_initializers
  in
  let tbb_cstr_init =
    let private_vars_args =
      VarSet.fold (fun vi argslist -> argslist@[FormalArg vi])
        tbb_class.private_vars []
    in
    let init_cstr_intializers =
      let private_vars_inits =
        List.map (fun vi -> (vi, LocalVar vi))
          (VarSet.elements tbb_class.private_vars)
      in
      private_vars_inits @ public_vars_inits
    in
    makeConstructor
      class_name
      tbb_class.ctype
      0
      private_vars_args
      (mkStmt (Instr []))
      init_cstr_intializers
  in
  (** TBB uses a method operator() that implements the loop body *)
  let tbb_operator =
    let operator_body_printer fmt ()  =
      let mod_loop_body, constant_assignments =
        remove_constant_assignments pb pb.main_loop_body
      in
      pp_operator_body fmt pb (index_var, begin_index_var, end_index_var)
        constant_assignments
        (fun fmt () ->
           fprintf fmt "@[%a@]@;"
             (pp_c_fnlet ~p_id_assign:false)
             (rename_bounds (fn_for_c mod_loop_body)))
    in
    let operator_arg =
      (fprintf str_formatter "const blocked_range<%s>& %s"
         iterator_type_name iterator_name;
       flush_str_formatter ())
    in
    {
      mid = 0;
      mtyp = TVoid [];
      mname = "operator()";
      mattributes = [];
      margs = [SpecialArg operator_arg];
      mcpp = true;
      mlocals = VarSet.empty;
      mbody = (mkStmt (Instr []));
      mprint = Some operator_body_printer;
    }
  in
  (** Join operation : the join method joins the current instance with another
      instance (the right state) *)
  let tbb_join =
    let join_body_printer fmt () =
      printing_for_join := true;
      cpp_class_members_set := tbb_class.public_vars;
      (* Translate parallel assignments : for now, go with the simplest
         solution which is using temporary variables *)
      fprintf fmt "%a@\n" (pp_c_fnlet ~p_id_assign:true)
        (fn_for_c pb.join_solution);
      (* Assign local variable value to class member *)
      VarSet.iter
        (fun vi ->
           fprintf fmt "@[%s%s = %s;@]@;"
             class_member_appendix vi.vname vi.vname)
        pb.scontext.state_vars;
      printing_for_join := false
    in
    let join_from_name = (Config.get_conf_string "tbb_right_state_name") in
    let join_args = [SpecialArg (class_name^"& "^join_from_name)] in
    {
      mid = 1;
      mtyp = TVoid [];
      mname = "join";
      mattributes = [];
      margs = join_args;
      mcpp = true;
      mlocals = pb.scontext.state_vars;
      mbody = (mkStmt (Instr []));
      mprint = Some join_body_printer;
    }
  in
  tbb_class.constructors <- [tbb_cstr_copy; tbb_cstr_init];
  tbb_class.public_members <- [tbb_operator; tbb_join];
  tbb_class

let fprint_sep fmt = fprintf fmt "@.@."

let test_class_name_of pb = "Test"^(String.capitalize (pbname_of_sketch pb))

let fprint_implementations fmt pb tbb_class =
  let test_cname = test_class_name_of pb in
  let class_var = String.lowercase ("_p_"^pb.loop_name^"_") in
  (* Use the init constructor here, and it must always have the id 0 *)
  let cstr_args =
    (List.find (fun cstr -> cstr.cid = 0)
       tbb_class.constructors).cargs
  in
  let return_type =
    let ret_typ =
      match convtype_of_v pb.host_function.fvar with
      | TFun (ret_typ, _, _, _) -> ret_typ
      | _ -> TVoid []
    in
    (Ct.psprint80 dn_type ret_typ)
  in
  let class_field =
    try
      (Ct.psprint80 dn_exp
         (IH.find Loops.return_exprs pb.host_function.fvar.vid))
    with Not_found -> "/* DON't KNOW WHAT TO RETURN */"
  in
  (* Print the parallel version of the loop *)
  fprintf fmt
    "@[<v 2>%s %s::parallel_apply() const {@\n\
     %s %s(%a);@\n\
     parallel_reduce(blocked_range<%s>(0,n,%s), %s);@\n\
     return %s.%s;@\n@]@\n}@\n"
    (* Return type of the function *)
    return_type
    (* Name of the examples and name of the current C++ class *)
    test_cname
    (* Name of the class containg the parallel implementation *)
    tbb_class.cname
    (* Name of the instance of the class *)
    class_var
    (* Arguments of the base constructor of the parallel class *)
    (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ", ")
       pp_constr_arg_in_app) cstr_args
    (* Other parameters *)
    iterator_type_name
    (Config.get_conf_string "tbb_chunk_size")
    class_var class_var class_field;

  (** Print the sequential version of the function *)
  fprintf fmt
    "@[<v 2>%s %s::sequential_apply() const {@\n\
     %a@\n\
     \* FILL THE BLOCK HERE *\;@\n\
     return %s;@\n@]@\n}@\n"
    (* Return type of the function *)
    return_type
    (* Name of the example and name of the class *)
    test_cname
    (* Assign local copy for all variables *)
    (fun fmt () ->
       VarSet.iter
         (fun vi ->
            fprintf fmt "%s %s = %s%s;@\n"
              (Ct.psprint80 dn_type (check_option (ciltyp_of_symb_type vi.vtype)))
              vi.vname
              class_member_appendix
              vi.vname)
         pb.scontext.all_vars) ()
    "sum"




let fprint_tbb_class fmt pb tbb_class =
  fprint_test_prelude fmt (pbname_of_sketch pb);
  pp_class fmt tbb_class;
  fprint_sep fmt;
  fprint_implementations fmt pb tbb_class


let output_tbb_test fname_of_sol solution =
  let tbb_file_oc =  open_out (fname_of_sol solution) in
  let tbb_file_out_fmt = Format.make_formatter
      (output tbb_file_oc) (fun () -> flush tbb_file_oc) in
  let tbb_class_summary = make_tbb_class solution in
  printf "New file: %s.@." (fname_of_sol solution);
  fprint_tbb_class tbb_file_out_fmt solution tbb_class_summary;
  close_out tbb_file_oc

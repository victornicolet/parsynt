open Format
open Cil

open PpHelper
open SketchTypes
open SPretty
open Utils

type problem =
  {
    pbname : string;
    vars : VS.t;
    lvars : VS.t;
    svars : VS.t;
    inits : skExpr IM.t;
    body : sklet;
    join : sklet;
  }



(** Class constructor argument *)
type cpp_constr_arg =
  | FormalArg of varinfo
  | FormalRefArg of varinfo
  | SpecialArg of string

let pp_cpp_constr_arg fmt =
  function
  | FormalArg vi ->
    fprintf fmt "%s %s"
      (CilTools.psprint80 dn_type vi.vtype) vi.vname
  | FormalRefArg vi ->
    fprintf fmt "%s& %s"
      (CilTools.psprint80 dn_type vi.vtype) vi.vname
  | SpecialArg s ->
    fprintf fmt "%s" s


(** Class constructor *)
type cpp_class_constr =
  {
    cid : int;
    ctype : typ;
    cname : string;
    cargs : cpp_constr_arg list;
    cbody : stmt;
    cinitializers : (varinfo * exp) list;
  }

let makeConstructor cn ct cid cargs cb cinit =
  { cid = cid; ctype = ct; cname = cn;
    cargs = cargs; cbody = cb; cinitializers = cinit;}

let print_initializer_list fmt li =
  ppli fmt ~sep:", "
    (fun fmt (vi, e) ->
    fprintf fmt "%s(%s)" vi.vname (CilTools.psprint80 dn_exp e))
    li

let pp_cpp_constructor fmt cpp_constructor =
  fprintf fmt "@[<hov 2>%s(%a)%a{@[hov 2>%s@]}@]"
    (* Constructor name *)
    cpp_constructor.cname
    (* Constructor arguments *)
    (fun f li -> ppli f ~sep:", " pp_cpp_constr_arg li) cpp_constructor.cargs
    (* Constructor initializers *)
    (fun fmt li ->
       if List.length li = 0 then fprintf fmt " "
       else
         fprintf fmt ": @[<hov 2>%a@]" print_initializer_list li)
    cpp_constructor.cinitializers
    (* Constructor body *)
    (CilTools.psprint80 dn_stmt cpp_constructor.cbody)


(** Class type *)
type cpp_class =
  {
    cname : string;
    ctype : typ;
    mutable private_vars : VS.t;
    mutable public_vars : VS.t;
    mutable constructors : cpp_class_constr list;
    mutable public_members : global list
  }

let makeEmptyClass class_name =
  let class_type =
    TNamed ({tname = "class_name"; ttype = TVoid []; treferenced = true}, [])
  in
  {
    cname = class_name;
    ctype = class_type;
    private_vars = VS.empty;
    public_vars = VS.empty;
    constructors = [];
    public_members = [];
  }

let pp_class fmt cls =
  let pp_members fmt vs =
    VS.iter
    (fun vi -> fprintf fmt "@[%s %s;@]@;"
        (CilTools.psprint80 Cil.dn_type vi.vtype) vi.vname)
    vs
  in
  let pp_class_body fmt cls =
    fprintf fmt "%a@;public:%a@;%a@;%a"
      pp_members cls.private_vars
      pp_members cls.public_vars
      (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ", ")
         pp_cpp_constructor) cls.constructors
      (pp_print_list
         ~pp_sep:(fun fmt () -> fprintf fmt ", ")
         (fun fmt fdec ->
            fprintf fmt "%s" (CilTools.psprint80 dn_global fdec)))
      cls.public_members
  in
  fprintf fmt "class %s{@[<hov 2>%a@]@;};"
    cls.cname
    pp_class_body cls

(** Specific use of the C++ class for our problem **)

let right_elt_name = ref "__right_t_"

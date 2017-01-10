open Format
open Cil

open PpHelper
open SketchTypes
open SPretty
open Utils

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

type cpp_constr_initializer = varinfo * init_expr
and init_expr =
  | ConstExpr of exp
  | ClassMember of varinfo * string
  | LocalVar of varinfo

let pp_initializer fmt (vi, init) =
  fprintf fmt "%s(%s)"
    vi.vname
    (match init with
     | ConstExpr  exp -> (CilTools.psprint80 dn_exp exp)
     | ClassMember (vi', s) -> vi.vname^"."^s
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
  fprintf fmt "@[<hov 2>%s(%a)%a{@[hov 2>%s@]}@]"
    (* Constructor name *)
    cpp_constructor.cname
    (* Constructor arguments *)
    (fun f li -> ppli f ~sep:", " pp_cpp_constr_arg li)
    cpp_constructor.cargs
    (* Constructor initializers *)
    (fun f li -> ppli f ~sep:", " pp_initializer li)
    cpp_constructor.cinitializers
    (* Constructor body *)
    (CilTools.psprint80 dn_stmt cpp_constructor.cbody)


(** Simplified methods : we don't use directly Cil's fundecs *)
type cpp_class_method =
  {
    mattributes : string list;
    mtyp : typ;
    mname : string;
    mid : int;
    mbody : stmt;
    mlocals : VS.t;
    mcpp : bool;
    mprint : (formatter -> unit) option;
  }

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
type problem =
  {
    pbname : string;
    vars : VS.t;
    lvars : VS.t;
    svars : VS.t;
    inits : skExpr IM.t;
    body : sklet;
    join : Ast.expr;
  }


let class_name_appendix = Conf.get_conf_string "class_name_appendix"
let class_member_appendix = Conf.get_conf_string "class_member_appendix"
let iterator_type_name = Conf.get_conf_string "tbb_iterator_type_name"

let pp_operator_body fmt pb ppbody =
  (* Local versions of the class's variables *)
  VS.iter
    (fun vi ->
       fprintf fmt "%s %s = my_%s;@;"
         (CilTools.psprint80 dn_type vi.vtype) vi.vname vi.vname) pb.vars;

  (* Bounds intialization *)
  fprintf fmt
    "if (b < 0 || r.begin() < b)\
     b = r.begin();\
     if (e < 0 || r.end() > e)\
     e = r.end();";
  (* Main loop *)
  fprintf fmt
    "for (%s i = r.begin(); i!= r.end(); ++i) {@;%a@;}"
    iterator_type_name ppbody ();
  (* Update class vars that need it *)
  VS.iter
    (fun vi ->
       fprintf fmt "my_%s = %s;@;" vi.vname vi.vname) pb.svars


let make_tbb_class pb =
  let class_name = class_name_appendix^pb.pbname in
  let tbb_class = makeEmptyClass class_name in
  let tbb_cstr_copy =
    makeConstructor
      class_name
      tbb_class.ctype
      0
      [] (* Args *)
      (mkStmt (Instr []))
      [] (* Intializers *)
  in
  let tbb_cstr_init =
    makeConstructor
      class_name
      tbb_class.ctype
      0
      [] (* Args *)
      (mkStmt (Instr []))
      [] (* Intializers *)
  in
  tbb_class.private_vars <- pb.lvars;
  tbb_class.public_vars <- pb.svars;
  tbb_class.constructors <- [tbb_cstr_copy; tbb_cstr_init];

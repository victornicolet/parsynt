open Cil
open Pretty
open List
open Printf
open Format

module S = Str

(** Set modules **)
module IntHash =
struct
  type t = int
  let equal i j = i=j
  let hash i = i land max_int
end

module IntHashTbl = Hashtbl.Make(IntHash)

module IH =
struct
  include IntHashTbl

  let copy_into to_copy into_copy =
    IntHashTbl.iter (IntHashTbl.add into_copy) to_copy

end


module IS = Set.Make (struct
    type t = int
    let compare = Pervasives.compare
  end)
module SM = Map.Make (String)

module VS = Usedef.VS
module IM = Map.Make(struct type t = int let compare = compare end)

(** Hash a set of variables with their variable id *)
let ih_of_vs vset =
  let ihs = IH.create 10 in
  VS.iter (fun v -> IH.add ihs v.vid v) vset;
  ihs

(**
    Returns a new hashset containing the the keys
    in h1, and values are the pairs of values
    having the same key in h1 and h2 (None for the second
    element if not found).
*)

let ih_join_left (newh : ('a * 'b option) IH.t)
    (h1 : 'a IH.t)  (h2 : 'b IH.t) : unit =
  IH.iter
    (fun k v1 ->
      try
        let v2 = IH.find h2 k in
        IH.add newh k (v1, Some v2)
      with Not_found -> IH.add newh k (v1, None)) h1

let identity x = x
let identity2 x y = y

let is_some = Core.Std.is_some
let is_none = Core.Std.is_none

(** Convert a varinfo to an expression *)
let v2e (v : varinfo): Cil.exp = Lval (var v)

let (|>) (a : 'a) (f: 'a -> 'b): 'b = f a
let (>>) (a : 'a list) (b : int) = List.nth a b

let map_2 (f : 'a -> 'b) ((a,b): ('a * 'a)) : ('b * 'b) = (f a, f b)

let map_3 (f : 'a -> 'b) ((a, b, c): ('a * 'a * 'a)) : ('b * 'b * 'b) =
  (f a, f b, f c)

let fst (a,b)  = a
let snd (a,b) = b


let bool_of_int64 i = i = 1L


let str_contains str sub = ExtLib.String.exists str sub;;

(** Lists *)
module ListTools = struct
  (** a -- b -- > list of integers from a to b *)
  let (--) i j =
    let rec aux n acc =
      if n < i then acc else aux (n-1) (n :: acc)
    in aux j []

  (**
      Returns the max of a list.
      /!\ The max of an empty list is min_int.
  *)
  let intlist_max li =
    List.fold_left
      (fun max elt -> if elt > max then elt else max)
      min_int
      li

  let lmin score_func l =
    let scored_list =
      List.map (fun elt -> (score_func elt, elt)) l in
    snd (List.hd
           (List.sort
              (fun (s1, _) (s2, _) ->
                 Pervasives.compare s1 s2)
              scored_list))



  let foldl_union f l =
    List.fold_left (fun set a -> VS.union set (f a)) VS.empty l

  let foldl_union2 f l =
    List.fold_left (fun (acc1, acc2) a ->
	  let s1, s2 = f a in (VS.union acc1 s1 , VS.union acc2 s2))
	  (VS.empty, VS.empty) l

  let pair a_li b_li =
    List.fold_left2
      (fun c_li a_elt b_elt -> c_li@[(a_elt, b_elt)]) []  a_li b_li

  let unpair a_b_li =
    List.fold_left
      (fun (a_li, b_li) (a, b) -> (a_li@[a], b_li@[b])) ([],[]) a_b_li

  let outer_join_lists (a, b) =
    List.fold_left
      (fun li i ->
        if List.mem i li then li else i::li) a b

  let last list =
    List.nth list ((List.length list) - 1)

  let remove_last list =
    match (List.rev list) with
    | h::t -> List.rev t
    | []   -> []

  let replace_last list elt =
    match (List.rev list) with
    | h::t -> List.rev (elt::t)
    | []   -> []

end



let last_instr instr_stmt =
  match instr_stmt.skind with
  | Instr il -> ListTools.last il
  | _ -> raise
     (Failure "last_instr expected a statement of instruction list kind" )

(** Simple function to check if the argument is {e Some a}.
    @param ao some argument of type 'a option
    @return the object in the option
    @raise Failure if the argument is None
*)
let check_option ao =
  match ao with
  | Some a -> a
  | None -> raise (Failure "check_option")

let maybe_apply (f:'a->'b) (v: 'a option) : 'b option =
  match v with
  | Some a -> Some (f a)
  | None -> None

let maybe_apply_default (f: 'a -> 'b) (v: 'a option) (default : 'b) : 'b =
  match v with
  | Some a -> f a
  | None -> default

let xorOpt o1 o2 =
  match o1, o2 with
  | None, Some a -> Some a
  | Some _, Some _ -> raise (Failure "xorOpt")
  | _, _ -> None


(** Get the function named fname in the file cf *)
let get_fun cf fname =
  let auxoptn cfile =
    Cil.foldGlobals cfile
      (fun fdeco g ->
        match g with
        | GFun (f, loc) ->
           begin
             if f.svar.vname = fname
             then xorOpt fdeco (Some f)
             else fdeco
           end
        | _ -> fdeco )
      None
  in
  try auxoptn cf
  with Failure s -> None

let non_empty_block (b : Cil.block) =
  (List.length b.bstmts) > 0

let global_filter_only_func fn g =
  match g with
  | GFun (f, loc) -> fn f
  | _ -> ()

let global_filter_only_funcLoc fn g =
  match g with
  | GFun (f, loc) -> fn f loc
  | _ -> ()

let appendC l a =
  List.append l
    (if List.mem a l then [] else [a])

(** Cil specific utility functions *)
(** Pretty printing shortcuts *)
module CilTools = struct
  let psprint80 f x = Pretty.sprint 80 (f () x)
  let ppe e = print_endline (psprint80 Cil.dn_exp e)
  let ppt t = print_endline (psprint80 Cil.d_type t)
  let pps s = print_endline ("Statement : "^(psprint80 Cil.dn_stmt s))
  let pplv lv = print_endline (psprint80 Cil.dn_lval lv)
  let ppv v = print_endline v.vname
  let ppi i = print_endline ("Instruction : "^(psprint80 Cil.dn_instr i))
  let ppbk blk = List.iter pps blk.bstmts
  let ppofs offs = print_endline (psprint80 (Cil.d_offset Pretty.nil) offs)

  let is_cil_temp vi =
    false

  let is_literal_zero = function
    | Const (CInt64 (0L, _, _)) -> true
    | _ -> false

  let add_stmt block stmt =
	{ block with bstmts = block.bstmts @ stmt }

  let simplify_rds rdef =
    match rdef with
    | Some (_,_, setXhash) -> Some setXhash
    | None -> None


  let neg_exp (exp : Cil.exp) =
    match exp with
    | UnOp (LNot, b, _) -> b
    | UnOp (Neg, x, _) -> x
    | _ -> UnOp (LNot, exp, TInt (IBool, []))

  let is_like_array (vi : Cil.varinfo) =
    match vi.vtype with
    | TPtr _ | TArray _ -> true
    | _ -> false

  let is_like_bool =
    function
    | IBool -> true
    | _ -> false

  let fun_ret_type tfunc =
    match tfunc with
    | TFun (ret_typ, _, _, _) -> Some ret_typ
    | _ -> None

  let rec is_of_bool_type vitype =
    match vitype with
    | TInt (ityp, _) -> is_like_bool ityp
    | f ->
      (match fun_ret_type f with
       | Some ftyp -> is_of_bool_type ftyp
       | None -> false )

  let is_of_real_type vitype =
    match vitype with
    | TFloat _ -> true
    | f -> (match fun_ret_type f with Some (TFloat _) -> true | _-> false)

  let rec is_of_int_type vitype =
    match vitype with
    | TInt _ -> not (is_of_bool_type vitype)
    | f -> (match fun_ret_type f with Some x -> is_of_real_type x | None -> false)

  let combine_expression_option op e1 e2 t=
    match e1, e2 with
    | Some e1, Some e2 -> Some (BinOp (op, e1, e2, t))
    | Some e1, None -> Some e1
    | None, Some e2 -> Some e2
    | None, None -> None

  let gen_var_with_suffix vi suffix =
    {vi with vname = vi.vname^suffix}

end
(**
    Extract the variables used in statements/expressions/instructions/..
    Used variables can be on either side of an assignment.
*)
module VSOps = struct
  let rec sovi (instr : Cil.instr) : VS.t =
    match instr with
    | Set (lval, exp, loc) ->
       let vs_ls = sovv lval in
       let vs_exp = sove exp in
       VS.union vs_exp vs_ls
    | Call (lvo, ef, elist, _) ->
       let vs_ls = maybe_apply_default sovv lvo VS.empty in
       let vs_el = ListTools.foldl_union sove elist in
       VS.union vs_ls vs_el
    | _ -> VS.empty

  and sove (expr : Cil.exp) : VS.t =
    match expr with
    | BinOp (_, e1, e2, _)
    | Question (_, e1, e2, _) -> VS.union (sove e1) (sove e2)
    | SizeOfE e | AlignOfE e | UnOp (_, e, _) | CastE (_, e) -> sove e
    | AddrOf v  | StartOf v | Lval v -> sovv v
    | SizeOfStr _ | AlignOf _ | AddrOfLabel _ | SizeOf _ | Const _ -> VS.empty

  and sovv ?(onlyNoOffset = false) (v : Cil.lval)  : VS.t =
    match v with
    | Var x, _ -> VS.singleton x
    | Mem e, offs -> VS.union (sove e)
       (if onlyNoOffset then VS.empty else (sovoff offs))

  and sovoff (off : Cil.offset) : VS.t =
    match off with
    | NoOffset -> VS.empty
    | Index (e, offs) -> VS.union (sove e) (sovoff offs)
    | Field _ -> VS.empty

  (** List to set and inverse functions *)

  let bindings (vs : VS.t) =
    VS.fold (fun v l -> l@[(v.vid, v)]) vs []

  let of_bindings (l : (int * VS.elt) list) : VS.t =
    List.fold_left (fun vs (k, v) -> VS.add v vs) VS.empty l


  let varlist (vs : VS.t) =
    VS.elements vs

  let of_varlist (l : VS.elt list) =
    VS.of_list l

  let namelist (vs : VS.t) =
    List.map (fun vi -> vi.vname) (varlist vs)

  (** Member testing functions *)

  let has_vid (id : int) (vs : VS.t) =
    VS.exists (fun vi -> vi.vid = id) vs

  let has_lval ((host,offset): lval) (vs: VS.t) =
    match host  with
    | Var vi -> has_vid vi.vid vs
    | _-> VS.cardinal
       (VS.inter (sovv ~onlyNoOffset:true (host,offset)) vs) > 1

  (** Get-element functions*)

  let find_by_id (id: int) (vs : VS.t) =
    if has_vid id vs then
      VS.min_elt (VS.filter (fun vi -> vi.vid = id) vs)
    else
      raise Not_found

  let subset_of_list (li : int list) (vs : VS.t) =
    VS.filter (fun vi -> List.mem vi.vid li) vs

  let vids_of_vs (vs : VS.t) : int list =
    List.map (fun vi -> vi.vid) (VS.elements vs)

  (** Set construction functions *)

  let unions (vsl : VS.t list) : VS.t =
    List.fold_left VS.union VS.empty vsl

  let union_map li f =
    List.fold_left (fun vs elt -> VS.union vs (f elt)) VS.empty li

  let vs_of_defsMap (dm : (Cil.varinfo * Reachingdefs.IOS.t option) IH.t) :
      VS.t =
    let vs = VS.empty in
    IH.fold (fun k (vi, rdo) vst -> VS.add vi vst) dm vs

  let vs_of_inthash ih =
    IH.fold (fun i vi set -> VS.add vi set) ih VS.empty

  let vs_with_suffix vs suffix =
    VS.fold
      (fun var new_vs ->
        VS.add (CilTools.gen_var_with_suffix var suffix) new_vs)
      vs
      VS.empty

  (** Pretty printing variable set *)

  let pp_var_names fmt (vs : VS.t) =
     let vi_list = varlist vs in
     pp_print_list
       ~pp_sep:(fun fmt () -> fprintf fmt " ")
       (fun fmt vi -> fprintf fmt "%s" vi.Cil.vname)
       fmt
       vi_list

  let to_string vs =
    (pp_var_names Format.str_formatter vs ; flush_str_formatter ())

  let pvs ppf (vs: VS.t) =
    if VS.cardinal vs > 0 then
      VS.iter
        (fun vi ->
           if vi.vistmp then
             Format.fprintf ppf "@[(%i : %s (tmp))@] @;" vi.vid vi.vname
           else
             Format.fprintf ppf "@[(%i : %s)@] @;" vi.vid vi.vname)
        vs
    else
      Format.fprintf ppf "%s@;" "{empty}"

  let ppvs vs = pvs Format.std_formatter vs
  let spvs vs = pvs Format.str_formatter vs; Format.flush_str_formatter ()
  let epvs vs = pvs Format.err_formatter vs

  let string_of_vs = spvs
end

module IHTools = struct

  let convert inthash =
    let ih = IH.create 10 in
    Inthash.iter (IH.add ih) inthash;
    ih

  (**
      Add al the key-value bindings of to_add to add_to only
      if the key is not present in add_to.
  *)
  let add_all add_to bindings_to_add =
    IH.iter
      (fun k v ->
         if IH.mem add_to k then () else IH.add add_to k v)
      bindings_to_add

  let add_list (add_to : 'a IH.t) (getk : 'a -> int) (l : 'a list) =
    List.iter (fun b -> IH.add add_to (getk b) b) l

  let iter_bottom_up
      (h : 'a IH.t)
      (isroot : 'a -> bool)
      (children : 'a -> 'a list)
      (app : 'a -> unit) : 'a list =
    let select_roots =
      IH.fold
        (fun k a roots ->
           if isroot a then a::roots else roots)
        h []
    in
    let rec build_botup stack acc =
      match stack with
      | [] -> acc
      | hd :: tl ->
        build_botup (tl@(children hd)) (hd::acc)
    in
    let upbots = build_botup select_roots [] in
    List.iter app upbots;
    upbots ;;

end

module IMTools = struct

  let add_all add_to to_add =
    IM.fold
      (fun k v mp ->
         if IM.mem k add_to then mp else
           IM.add k v mp)
      to_add add_to

  let update_all add_to to_add =
    IM.fold
      (fun k v mp -> IM.add k v mp)
      to_add add_to


  let inter a b =
    IM.fold
      (fun k v mp ->
         if IM.mem k a
         then IM.add k v b
         else mp)
      b
      IM.empty

  let is_disjoint ?(non_empty = (fun k v -> true)) a b=
    try
      IM.fold
        (fun k v bol ->
           if non_empty k v
           then
             (if IM.mem k a
              then failwith "iom"
              else bol)
           else bol)
        b
        true
    with Failure s -> false

  let disjoint_sets im1 im2 =
    let im1_in_im2 =
      IM.fold
        (fun k v map ->
           if IM.mem k im2 then IM.add k v map else map)
        im1 IM.empty
    in
    let im2_in_im1 =
      IM.fold
        (fun k v map ->
           if IM.mem k im1 then IM.add k v map else map)
        im2 IM.empty
    in
    let im1_only =
      IM.fold
        (fun k v map ->
           if IM.mem k im2 then map else IM.add k v map)
        im1 IM.empty
    in
    let im2_only =
      IM.fold
        (fun k v map ->
           if IM.mem k im1 then map else IM.add k v map)
        im2 IM.empty
    in
    im1_in_im2, im2_in_im1, im1_only, im2_only

end

module SMTools = struct
  let update map key nval update =
    try
      let pval = SM.find key map in
      SM.add key (update pval nval) map
    with Not_found ->
      SM.add key nval map
end

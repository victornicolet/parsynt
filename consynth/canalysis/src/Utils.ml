open Cil
open Pretty
open List
open Printf
open Format

module E = Errormsg
module S = Str
module IH = Inthash
module IS = Set.Make (struct
  type t = int
  let compare = Pervasives.compare
end)
module SM = Map.Make (String)

module VS = Usedef.VS
module IM = Map.Make(struct type t = int let compare = compare end)

(** Hash a set of variables with their variable id *)
let hashVS vset =
  let ihs = IH.create 10 in
  VS.iter (fun v -> IH.add ihs v.vid v) vset;
  ihs

(**
    Returns a new hashset containing the the keys
    in h1, and values are the pairs of values
    having the same key in h1 and h2 (None for the second
    element if not found).
*)

let addHash (newh : ('a * 'b option) IH.t)
    (h1 : 'a IH.t)  (h2 : 'b IH.t) : unit =
  IH.iter
    (fun k v1 ->
      try
        let v2 = IH.find h2 k in
        IH.add newh k (v1, Some v2)
      with Not_found -> IH.add newh k (v1, None)) h1

let identity x = x
let identity2 x y = y

(** Convert a varinfo to an expression *)
let v2e (v : varinfo): Cil.exp = Lval (var v)

let (|>) (a : 'a) (f: 'a -> 'b): 'b = f a

let map_2 (f : 'a -> 'b) ((a,b): ('a * 'a)) : ('b * 'b) = (f a, f b)

let map_3 (f : 'a -> 'b) ((a, b, c): ('a * 'a * 'a)) : ('b * 'b * 'b) =
  (f a, f b, f c)

(** Lists *)
module ListTools = struct

  let foldl_union (f: 'a -> VS.t) (l: 'a list) : VS.t =
    List.fold_left (fun set a -> VS.union set (f a)) VS.empty l

  let foldl_union2 (f: 'a -> VS.t * VS.t) (l: 'a list) : VS.t * VS.t =
    List.fold_left (fun (acc1, acc2) a ->
	  let s1, s2 = f a in (VS.union acc1 s1 , VS.union acc2 s2))
	  (VS.empty, VS.empty) l


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



let lastInstr instr_stmt =
  match instr_stmt.skind with
  | Instr il -> ListTools.last il
  | _ -> raise
     (Failure "lastInstr expected a statement of instruction list kind" )

let checkOption (ao : 'a option) : 'a =
  match ao with
  | Some a -> a
  | None -> raise (Failure "checkOption")

let appOption (f: 'a -> 'b) (v: 'a option) (default : 'b) : 'b =
  match v with
  | Some a -> f a
  | None -> default

let xorOpt o1 o2 =
  match o1, o2 with
  | None, Some a -> Some a
  | Some _, Some _ -> raise (Failure "xorOpt")
  | _, _ -> None


(** Get the function named fname in the file cf *)
let getFn cf fname =
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

let onlyFunc fn g =
  match g with
  | GFun (f, loc) -> fn f
  | _ -> ()

let onlyFuncLoc fn g =
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

  let setOfReachingDefs rdef =
    match rdef with
    | Some (_,_, setXhash) -> Some setXhash
    | None -> None

  let getBody stmt =
    match stmt.skind with
    | Loop (blk, _, _, _) -> blk.bstmts
    | _ -> []

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

  let bool_of_int64 i = (i = (Int64.of_int 1))

  let rec get_host_var host =
    match host with
    | Var vi -> Some vi
    | Mem e ->
       (match e with
       | Lval (hst, offset) -> get_host_var hst
       | BinOp (op, e1, e2, t) ->
          get_var e1
       | _ -> None
       )
  and get_var e =
    match e with
    | Lval (host,offset) -> get_host_var host
    | _ -> None
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
       let vs_ls = appOption sovv lvo VS.empty in
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

  let bindings (vs : VS.t) =
    VS.fold (fun v l -> l@[(v.vid, v)]) vs []

  let of_bindings (l : (int * VS.elt) list) : VS.t =
    List.fold_left (fun vs (k, v) -> VS.add v vs) VS.empty l

  let varlist (vs : VS.t) =
    VS.elements vs
  let of_varlist (l : VS.elt list) =
    VS.of_list l

  let hasVid (id : int) (vs : VS.t) =
    VS.exists (fun vi -> vi.vid = id) vs

  let hasLval ((host,offset): lval) (vs: VS.t) =
    match host  with
    | Var vi -> hasVid vi.vid vs
    | _-> VS.cardinal (VS.inter (sovv ~onlyNoOffset:true (host,offset)) vs) > 1

  let getVi (id: int) (vs : VS.t) =
    VS.min_elt (VS.filter (fun vi -> vi.vid = id) vs)

  let subset_of_list (li : int list) (vs : VS.t) =
    VS.filter (fun vi -> List.mem vi.vid li) vs

  let unions (vsl : VS.t list) : VS.t =
    List.fold_left VS.union VS.empty vsl

  let vs_of_defsMap (dm : (Cil.varinfo * Reachingdefs.IOS.t option) IH.t) :
      VS.t =
    let vs = VS.empty in
    IH.fold (fun k (vi, rdo) vst -> VS.add vi vst) dm vs

  let vs_of_inthash ih =
    IH.fold (fun i vi set -> VS.add vi set) ih VS.empty

  let vids_of_vs (vs : VS.t) : int list =
    List.map (fun vi -> vi.vid) (VS.elements vs)

  let pvs ppf (vs: VS.t) =
    if VS.cardinal vs > 0 then
      VS.iter
        (fun vi -> Format.fprintf ppf "@[(%i : %s)@] @;" vi.vid vi.vname)
        vs
    else
      Format.fprintf ppf "%s@;" "{empty}"

  let ppvs vs = pvs Format.std_formatter vs
  let spvs vs = pvs Format.str_formatter vs; Format.flush_str_formatter ()
  let epvs vs = pvs Format.err_formatter vs

  let string_of_vs vs = pvs str_formatter vs ; flush_str_formatter ()
  let ppvs = pvs std_formatter
  let epvs = pvs err_formatter
end

module IHTools = struct
    (**
        Add al the key-value bindings of to_add to add_to only
        if the key is not present in add_to.
    *)
    let add_all add_to to_add =
      IH.iter
        (fun k v ->
          if IH.mem add_to k then () else IH.add add_to k v)
        to_add

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
end

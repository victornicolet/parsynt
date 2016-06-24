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

module VS = Usedef.VS

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

(** Convert a varinfo to an expression *)
let v2e (v : varinfo): Cil.exp = Lval (var v)

let (|>) (a : 'a) (f: 'a -> 'b): 'b = f a

let map_2 (f : 'a -> 'b) ((a,b): ('a * 'a)) : ('b * 'b) = (f a, f b)

let map_3 (f : 'a -> 'b) ((a, b, c): ('a * 'a * 'a)) : ('b * 'b * 'b) =
  (f a, f b, f c)

(** Lists *)

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

let lastInstr instr_stmt =
  match instr_stmt.skind with
  | Instr il -> last il
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
let psprint80 f x = Pretty.sprint 80 (f () x)
let ppe e = print_endline (psprint80 Cil.dn_exp e)
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

(**
    Extract the variables used in statements/expressions/instructions/..
    Used variables can be on either side of an assignment.
*)

let rec sovi (instr : Cil.instr) : VS.t =
  match instr with
  | Set (lval, exp, loc) ->
     let vs_ls = sovv lval in
     let vs_exp = sove exp in
     VS.union vs_exp vs_ls
  | Call (lvo, ef, elist, _) ->
     let vs_ls = appOption sovv lvo VS.empty in
     let vs_el = foldl_union sove elist in
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

let hasVid (id : int) (vs : VS.t) =
  VS.exists (fun vi -> vi.vid = id) vs

let getVi (id: int) (vs : VS.t) =
 VS.min_elt (VS.filter (fun vi -> vi.vid = id) vs)

let subset_of_list (li : int list) (vs : VS.t) =
  VS.filter (fun vi -> List.mem vi.vid li) vs

let vs_of_defsMap (dm : (Cil.varinfo * Reachingdefs.IOS.t option) IH.t) :
    VS.t =
  let vs = VS.empty in
  IH.fold (fun k (vi, rdo) vst -> VS.add vi vst) dm vs

let vids_of_vs (vs : VS.t) : int list =
  List.map (fun vi -> vi.vid) (VS.elements vs)

let pvs ppf (vs: VS.t) =
  VS.iter
    (fun vi -> fprintf ppf "@[(%i : %s)@] @;" vi.vid vi.vname)
    vs

let string_of_vs vs = pvs str_formatter vs ; flush_str_formatter ()
let ppvs = pvs std_formatter
let epvs = pvs err_formatter

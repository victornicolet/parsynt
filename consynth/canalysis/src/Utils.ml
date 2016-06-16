open Cil
open Pretty
open List

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
let addHash newh h1 h2 =
  IH.iter
    (fun k v1 -> 
      try 
        let v2 = IH.find h2 k in
        IH.add newh k (v1, Some v2)
      with Not_found -> IH.add newh k (v1, None)) h1

let v2e (v : varinfo): exp = Lval (var v)

let (|>) (a : 'a) (f: 'a -> 'b): 'b = f a

let map_2 (f : 'a -> 'b) ((a,b): ('a * 'a)) : ('b * 'b) = (f a, f b)

let map_3 (f : 'a -> 'b) ((a, b, c): ('a * 'a * 'a)) : ('b * 'b * 'b) = 
  (f a, f b, f c)

let checkOption (ao : 'a option) : 'a =
  match ao with
  | Some a -> a
  | None -> raise (Failure "checkOption")


let xorOpt o1 o2 =
  match o1, o2 with
  | None, Some a -> Some a
  | Some _, Some _ -> raise (Failure "xorOpt")
  | _, _ -> None

let getFn cf fname =
  let auxoptn cfile =
    Cil.foldGlobals cfile
      (fun fdeco g ->
        match g with
        | GFun (f, loc) ->
           begin
             if f.svar.vname == fname 
             then xorOpt fdeco (Some f)
             else fdeco
           end
        | _ -> fdeco )
      None 
  in
  try auxoptn cf 
  with Failure s -> None


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
let setOfReachingDefs rdef =
  match rdef with
  | Some (_,_, setXhash) -> Some setXhash
  | None -> None

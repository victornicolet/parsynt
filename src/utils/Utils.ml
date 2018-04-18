(**
   This file is part of Parsynt.

   Author: Victor Nicolet <victorn@cs.toronto.edu>

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

open Cil
open Pretty
open List
open Printf
open Format
open Sets

module IH = Sets.IH
module IS = Sets.IS
module SM = Sets.SM


let failhere file f s = failwith (sprintf "[%s][%s]: %s@." file f s)

let try_not_found f m = try f with Not_found -> print_endline m

(** Hash a set of variables with their variable id *)
let ih_of_vs vset =
  let ihs = IH.create 10 in
  VSo.iter (fun v -> IH.add ihs v.vid v) vset;
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

let is_some = function Some _ -> true | _ -> false
let is_none = function None -> true | _ -> false

(** Convert a varinfo to an expression *)
let v2e (v : varinfo): Cil.exp = Lval (var v)

let (==>) (f: 'a -> 'b) (xo : 'a option) =
  match xo with
  | Some x -> Some (f x)
  | None -> None

let (|>) (a : 'a) (f: 'a -> 'b): 'b = f a
let (>>) (a : 'a list) (b : int) = List.nth a b
let foi = float_of_int
let fos = float_of_string

let (-->) (f : 'a -> 'a) (g : 'a -> 'a) = (fun x -> g (f x))

let (<=>) (f : 'a -> 'a) (g : 'a -> 'a) = (fun x -> f x = g x)


let map_2 (f : 'a -> 'b) ((a,b): ('a * 'a)) : ('b * 'b) = (f a, f b)

let map_3 (f : 'a -> 'b) ((a, b, c): ('a * 'a * 'a)) : ('b * 'b * 'b) =
  (f a, f b, f c)

let fst (a,b)  = a
let snd (a,b) = b

(* Mutable conditionals for actions. *)
let _brev b = b := not !b
let _boff b = b := false
let _bon b = b := true
(* If flag true then do nothing, else do and set flag to true. *)
let (-?) b f = if !b then () else (_bon b; f)
(* If flag true then do and set flag to false, else do nothing *)
let (+?) b f = if !b then (_boff b; f) else ()


let bool_of_int64 i = i = 1L

let str_contains str sub = ExtLib.String.exists str sub;;
let str_begins_with sub str = ExtLib.String.starts_with str sub;;
(** Lists *)
module ListTools = struct
  open List
  (** a -- b -- > list of integers from a to b *)
  let (--) i j =
    if i <= j then
      let rec aux n acc =
        if n < i then acc else aux (n-1) (n :: acc)
      in aux j []
    else []

  let init (len : int) (f: int -> 'a) : 'a list =
    let rec aux_init l i =
      if i <= 0 then (f 0)::l else (aux_init ((f i)::l) (i -1))
    in aux_init [] len

  let mapoption (f: 'a -> 'b option) (l : 'a list) : 'b list =
    List.map (function Some x -> x | _ -> failwith "x")
      (List.filter is_some (List.map f l))

  (* Generate all k-length subslists of list l *)
  let k_combinations n lst =
    let rec inner acc k lst =
      match k with
      | 0 -> [[]]
      | _ ->
        match lst with
        | []      -> acc
        | x :: xs ->
          let rec accmap acc f = function
            | []      -> acc
            | x :: xs -> accmap ((f x) :: acc) f xs
          in
          let newacc = accmap acc (fun z -> x :: z) (inner [] (k - 1) xs)
          in
          inner newacc k xs
    in
    inner [] n lst

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
    List.fold_left (fun set a -> VSo.union set (f a)) VSo.empty l

  let foldl_union2 f l =
    List.fold_left (fun (acc1, acc2) a ->
	let s1, s2 = f a in (VSo.union acc1 s1 , VSo.union acc2 s2))
      (VSo.empty, VSo.empty) l

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

let somes l = List.map check_option (List.filter is_some l)

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
module CilTools = CilTop
(**
    Extract the variables used in statements/expressions/instructions/..
    Used variables can be on either side of an assignment.
*)
module VS = struct
  include VSo
  let rec sovi (instr : Cil.instr) : t =
    match instr with
    | Set (lval, exp, loc) ->
      let vs_ls = sovv lval in
      let vs_exp = sove exp in
      union vs_exp vs_ls
    | Call (lvo, ef, elist, _) ->
      let vs_ls = maybe_apply_default sovv lvo empty in
      let vs_el = ListTools.foldl_union sove elist in
      union vs_ls vs_el
    | _ -> empty

  and sove (expr : Cil.exp) : t =
    match expr with
    | BinOp (_, e1, e2, _)
    | Question (_, e1, e2, _) -> union (sove e1) (sove e2)
    | SizeOfE e | AlignOfE e | UnOp (_, e, _) | CastE (_, e) -> sove e
    | AddrOf v  | StartOf v | Lval v -> sovv v
    | SizeOfStr _ | AlignOf _ | AddrOfLabel _ | SizeOf _ | Const _ -> empty

  and sovv ?(onlyNoOffset = false) (v : Cil.lval)  : t =
    match v with
    | Var x, _ -> singleton x
    | Mem e, offs -> union (sove e)
                       (if onlyNoOffset then empty else (sovoff offs))

  and sovoff (off : Cil.offset) : t =
    match off with
    | NoOffset -> empty
    | Index (e, offs) -> union (sove e) (sovoff offs)
    | Field _ -> empty

  (** List to set and inverse functions *)

  let bindings (vs : t) =
    fold (fun v l -> l@[(v.vid, v)]) vs []

  let of_bindings (l : (int * elt) list) : t =
    List.fold_left (fun vs (k, v) -> add v vs) empty l


  let varlist (vs : t) =
    elements vs

  let of_varlist (l : elt list) =
    of_list l

  let vsmap f (vs : t) =
    map f (varlist vs)

  let namelist (vs : t) =
    List.map (fun vi -> vi.vname) (varlist vs)

  let vids_of_vs (vs : t) : int list =
    List.map (fun vi -> vi.vid) (elements vs)

  let vidset_of_vs vs =
    IS.of_list (vids_of_vs vs)
  (** Member testing functions *)

  let has_vid (id : int) (vs : t) =
    exists (fun vi -> vi.vid = id) vs

  let has_lval ((host,offset): lval) (vs: t) =
    match host  with
    | Var vi -> has_vid vi.vid vs
    | _-> cardinal
            (inter (sovv ~onlyNoOffset:true (host,offset)) vs) > 1

  (** Get-element functions*)

  let find_by_id (id: int) (vs : t) =
    if has_vid id vs then
      min_elt (filter (fun vi -> vi.vid = id) vs)
    else
      raise Not_found

  let find_by_name (name : string) (vs : t) =
    let matchings = filter (fun vi -> vi.vname = name) vs in
    match cardinal matchings with
    | 0 -> raise Not_found
    | 1 -> min_elt matchings
    | _ -> raise
             (Failure
                (Format.fprintf str_formatter
                   "More than one variable named %s" name;
                 Format.flush_str_formatter ()))

  let subset_of_list (li : int list) (vs : t) =
    filter (fun vi -> List.mem vi.vid li) vs

  (** Set construction functions *)

  let unions (vsl : t list) : t =
    List.fold_left union empty vsl

  let union_map li f =
    List.fold_left (fun vs elt -> union vs (f elt)) empty li

  let vs_of_defsMap (dm : (Cil.varinfo * Reachingdefs.IOS.t option) IH.t) :
    t =
    let vs = empty in
    IH.fold (fun k (vi, rdo) vst -> add vi vst) dm vs

  let vs_of_inthash ih =
    IH.fold (fun i vi set -> add vi set) ih empty

  let vs_with_suffix vs suffix =
    fold
      (fun var new_vs ->
         add (CilTools.gen_var_with_suffix var suffix) new_vs)
      vs
      empty

  let vs_with_prefix vs prefix =
    fold
      (fun var new_vs ->
         add (CilTools.gen_var_with_prefix var prefix) new_vs)
      vs
      empty


  (** Pretty printing variable set *)

  let pp_var_names fmt (vs : t) =
    let vi_list = varlist vs in
    pp_print_list
      ~pp_sep:(fun fmt () -> fprintf fmt " ")
      (fun fmt vi -> fprintf fmt "%s" vi.Cil.vname)
      fmt
      vi_list

  let to_string vs =
    (pp_var_names Format.str_formatter vs ; flush_str_formatter ())

  let pvs ppf (vs: t) =
    if cardinal vs > 0 then
      iter
        (fun vi ->
           if vi.vistmp then
             Format.fprintf ppf "@[(%i : %s (-tmp-))@]@" vi.vid vi.vname
           else
             Format.fprintf ppf "@[(%i : %s)@]@;" vi.vid vi.vname)
        vs
    else
      Format.fprintf ppf "%s@;" "{empty}"

  let ppvs vs = pvs Format.std_formatter vs
  let spvs vs = pvs Format.str_formatter vs; Format.flush_str_formatter ()
  let epvs vs = pvs Format.err_formatter vs

  let string_of_vs = spvs
end

module IHTools = struct
  (* Converts Inthash.t to IH.t. Yes, it's different. *)
  let convert inthash =
    let ih = IH.create 10 in
    Inthash.iter (IH.add ih) inthash;
    ih

  let key_list ih = IH.fold (fun k _ l -> k::l) ih []


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

module IntegerMap = Map.Make(struct type t = int let compare = compare end)
module IM = struct
  include IntegerMap

  let keyset imt =
    IS.of_list (List.map (fun (a,b) -> a) (IntegerMap.bindings imt))

  let add_all add_to to_add =
    IntegerMap.fold
      (fun k v mp ->
         if IntegerMap.mem k add_to then mp else
           IntegerMap.add k v mp)
      to_add add_to

  let update_all add_to to_add =
    IntegerMap.fold
      (fun k v mp -> IntegerMap.add k v mp)
      to_add add_to


  let inter a b =
    IntegerMap.fold
      (fun k v mp ->
         if IntegerMap.mem k a
         then IntegerMap.add k v b
         else mp)
      b
      IntegerMap.empty

  let is_disjoint ?(non_empty = (fun k v -> true)) a b=
    try
      IntegerMap.fold
        (fun k v bol ->
           if non_empty k v
           then
             (if IntegerMap.mem k a
              then failwith "iom"
              else bol)
           else bol)
        b
        true
    with Failure s -> false

  let disjoint_sets im1 im2 =
    let im1_in_im2 =
      IntegerMap.fold
        (fun k v map ->
           if IntegerMap.mem k im2 then IntegerMap.add k v map else map)
        im1 IntegerMap.empty
    in
    let im2_in_im1 =
      IntegerMap.fold
        (fun k v map ->
           if IntegerMap.mem k im1 then IntegerMap.add k v map else map)
        im2 IntegerMap.empty
    in
    let im1_only =
      IntegerMap.fold
        (fun k v map ->
           if IntegerMap.mem k im2 then map else IntegerMap.add k v map)
        im1 IntegerMap.empty
    in
    let im2_only =
      IntegerMap.fold
        (fun k v map ->
           if IntegerMap.mem k im1 then map else IntegerMap.add k v map)
        im2 IntegerMap.empty
    in
    im1_in_im2, im2_in_im1, im1_only, im2_only

  let of_ih ih = IH.fold (fun k l m -> IntegerMap.add k l m) ih IntegerMap.empty
end

module PpTools = struct
  let colorPrefix = "\x1b"

  let colormap =
    List.fold_left2
      (fun m k v -> SM.add k (colorPrefix^v) m)
      SM.empty
      ["black"; "red"; "green"; "yellow"; "blue"; "violet"; "cyan"; "white";
       "i"; "u"; "b"; "grey";
       "b-grey"; "b-red"; "b-green"; "b-yellow";"b-blue"; "b-violet"; "b-cyan";
       "b-white"; "b-lightgray"; "b-brown";
       "hi-underlined"; "hi-blinking"; "hi-inverted"; "hi-concealed"]
      ["[30m"; "[31m"; "[32m"; "[33m"; "[34m"; "[35m"; "[36m"; "[37m";
       "[3m"; "[4m"; "[1m"; "[2m";
       "[100m"; "[101m"; "[102m"; "[103m";"[104m"; "[105m"; "[106m"; "[107m";
       "[47m"; "[43m";
       "[4m"; "[5m"; "[7m"; "[8m"]

  let color cname =
    try
      SM.find cname colormap
    with Not_found -> colorPrefix^"[0m"

  let color_default = colorPrefix^"[0m"

  let pp_newline fmt () = fprintf fmt "@."

  (** List printing *)

  let rec ppli
      (ppf : formatter)
      ?(sep = ";")
      (pfun : formatter -> 'a -> unit) : 'a list -> unit =
    pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "%s" sep) pfun ppf

  let pp_int_list ppf =
    ppli ppf
      ~sep:":"
      (fun ppf i -> fprintf ppf "%i" i)

  let print_int_list = pp_int_list std_formatter

  let pp_string_list fmt =
    ppli fmt ~sep:" " (fun fmt s -> fprintf fmt "%s" s)

  let pp_comma_sep_list pf fmt =
    pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ", ") pf fmt

  let pp_sep_nl fmt () = fprintf fmt "@."
  let pp_sep_comma fmt () = fprintf fmt ", "
  let pp_sep_brk fmt () = fprintf fmt "@;"

  (** Map printing *)
  let ppimap
      (pelt : formatter -> 'a -> unit)
      (ppf : formatter) : 'a IM.t -> unit =
    IM.iter
      (fun i a ->
         fprintf ppf "@[<hov 2> %i -> %a@]@;" i pelt a)

  let ppifmap
      (pi : formatter -> int -> unit)
      (pelt : formatter -> 'a -> unit)
      (ppf : formatter) : 'a IM.t -> unit =
    IM.iter
      (fun i a ->
         fprintf ppf "@[<hov 2> %a <- %a@]@;" pi i pelt a)


  let string_of_loc (loc : Cil.location) =
    sprintf "<#line %i in %s, byte %i>" loc.Cil.line loc.Cil.file loc.Cil.byte

  let loc_of_string loca =
    let regexp =
      Str.regexp "<#line \\([0-9]+\\) in \\([0-9A-Za-z\\._-]+\\), byte \\([0-9]+>\\)"
    in
    try
      ignore(Str.search_forward regexp loca 0);
      let line = int_of_string (Str.matched_group 0 loca) in
      let file_name = Str.matched_group 1 loca in
      let byte =  int_of_string (Str.matched_group 2 loca) in
      Some { Cil.line = line; file = file_name; Cil.byte = byte }
    with Not_found -> None


  (** Hastable printing *)
  let pp_hash fmt print_elt htbl =
    let pp_elts fmt () =
      IH.iter (fun k elt -> fprintf fmt "(%i:%a)@;" k print_elt elt) htbl
    in
    fprintf fmt "@[<hv 2><HashTable:@;%a>@]" pp_elts ()

  (**TODO : replace characters that are setting color back to default in incoming
     string *)
  let printerr s =
    Format.fprintf err_formatter "%s%s%s" (color "red") s color_default

  let print_err_std s =
    Format.fprintf std_formatter "%s!%s %s%s%s"
      (color "b-red") color_default
      (color "red") s color_default
end


let list_array_map f l =
  Array.to_list (Array.map f (Array.of_list l))

let rec count_map f l ctr =
  match l with
  | [] -> []
  | [x] -> [f x]
  | [x;y] ->
    (* order matters! *)
    let x' = f x in
    let y' = f y in
    [x'; y']
  | [x;y;z] ->
    let x' = f x in
    let y' = f y in
    let z' = f z in
    [x'; y'; z']
  | x :: y :: z :: w :: tl ->
    let x' = f x in
    let y' = f y in
    let z' = f z in
    let w' = f w in
    x' :: y' :: z' :: w' ::
    (if ctr > 500 then list_array_map f tl
     else count_map f tl (ctr + 1))

let list_map f l = count_map f l 0

let equals x1 x2 : bool =
  (compare x1 x2) = 0


let print_defs vs defsHash =
  IH.iter
    (fun k ios ->
       let stmts =
         let def_ids =
           List.map (fun os -> match os with Some o -> o | None -> failwith "X")
             (List.filter (fun os -> match os with Some _ -> true | _ -> false)
                  (IOS.elements ios))
         in
         List.map
           (fun def_id ->
              IH.find (IHTools.convert Reachingdefs.ReachingDef.defIdStmtHash)
                def_id)
           def_ids
       in
       printf "Reaching defs for %s:@.@[<h 2>%a@]@."
         (try (VS.find_by_id k vs).vname with Not_found -> "??")
         (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "@;")
            (fun fmt stmt ->
               fprintf fmt "%s" (CilTools.psprint80 Cil.dn_stmt stmt)))
         stmts)
    defsHash

(* From  http://www.wiki.crossplatform.ru *)

(* OCaml does not come with a globbing function. As a workaround, the
   following function builds a regular expression from a glob pattern.
   Only the '*' and '?' wildcards are recognized. *)
open Str

let regexp_of_glob pat =
  Str.regexp
    (Printf.sprintf "^%s$"
       (String.concat ""
          (List.map
             (function
                | Str.Text s -> Str.quote s
                | Str.Delim "*" -> ".*"
                | Str.Delim "?" -> "."
                | Str.Delim _ -> assert false)
             (Str.full_split (Str.regexp "[*?]") pat))))

(* Now we can build a very basic globber. Only the filename part will
   be used in the glob pattern, so directory wildcards will break in
   this simple example. *)
let glob pat =
  let basedir = Filename.dirname pat in
  let files = Sys.readdir basedir in
  let regexp = regexp_of_glob (Filename.basename pat) in
  List.map
    (Filename.concat basedir)
    (List.filter
       (fun file -> Str.string_match regexp file 0)
       (Array.to_list files))

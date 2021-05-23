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

open Base
module IH = Sets.IH
module IS = Sets.IS
module SM = Sets.SM
module SH = Sets.SH
module IM = Sets.IM
module Config = Config
module Log = Log
module Naming = Naming

let failhere file f s =
  failwith Fmt.(to_to_string (fun frmt () -> pf frmt "[%s][%s]: %s@." file f s) ())

let try_not_found f m = try f with Caml.Not_found -> Fmt.(pf stdout "%s" m)

let identity x = x

let identity2 _ y = y

let is_some = function Some _ -> true | _ -> false

let is_none = function None -> true | _ -> false

let ( ==> ) (f : 'a -> 'b) (xo : 'a option) = match xo with Some x -> Some (f x) | None -> None

let ( |> ) (a : 'a) (f : 'a -> 'b) : 'b = f a

let ( >> ) (a : 'a list) (b : int) = List.nth a b

let ( @: ) (a : 'a list) (b : int) = List.nth a b

let foi = Float.of_int

let fos = Float.of_string

let ( --> ) (f : 'a -> 'b) (g : 'b -> 'c) x = g (f x)

let ( <=> ) (f : 'a -> 'a) (g : 'a -> 'a) x = f x = g x

let map_2 (f : 'a -> 'b) ((a, b) : 'a * 'a) : 'b * 'b = (f a, f b)

let map_3 (f : 'a -> 'b) ((a, b, c) : 'a * 'a * 'a) : 'b * 'b * 'b = (f a, f b, f c)

let fst (a, _) = a

let snd (_, b) = b

let fst3 (a, _, _) = a

let f2of3 (a, b, _) = (a, b)

let snd3 (_, b, _) = b

let third (_, _, c) = c

(* Mutable conditionals for actions. *)
let _brev b = b := not !b

let _boff b = b := false

let _bon b = b := true

(* If flag true then do nothing, else do and set flag to true. *)
let ( -? ) b f =
  if !b then ()
  else (
    _bon b;
    f)

(* If flag true then do and set flag to false, else do nothing *)
let ( +? ) b f =
  if !b then (
    _boff b;
    f)
  else ()

(* Set operations *)
let ( -$ ) is1 is2 = Set.diff is1 is2

let ( +$ ) is1 is2 = Set.union is1 is2

let ( ~$ ) i = Set.singleton (module Int) i

let ( !$ ) s = Set.max_elt s

let ( ?$ ) s = Set.length s

let bool_of_int64 i = Int64.(i = 1L)

let str_contains str sub = String.is_substring str ~substring:sub

let str_begins_with sub str = String.is_prefix ~prefix:sub str

let str_ends_with sub str = String.is_suffix ~suffix:sub str

(** Lists *)
module ListTools = struct
  open List

  let ( -- ) i j =
    if i <= j then
      let rec aux n acc = if n < i then acc else aux (n - 1) (n :: acc) in
      aux j []
    else []

  (** Generate all pairs of distrinct elements in list *)
  let rec all_pairs lst =
    match lst with [] -> [] | hd :: tl -> List.map ~f:(fun t -> (hd, t)) tl @ all_pairs tl

  let cartesian3 l1 l2 l3 =
    List.map ~f:(fun x -> List.map ~f:(fun y -> List.map ~f:(fun z -> (x, y, z)) l3) l2) l1

  let deindex l = List.map ~f:(fun (_, t) -> t) l

  let for_all_i pred l = List.for_all ~f:pred (List.mapi ~f:(fun i e -> (i, e)) l)

  let index l = List.mapi ~f:(fun i t -> (i, t)) l

  let init (len : int) (f : int -> 'a) : 'a list =
    let rec aux_init l i = if i <= 0 then f 0 :: l else aux_init (f i :: l) (i - 1) in
    aux_init [] len

  (**
     [is_prefix_sublist pre l] returns [true] if [pre] is a prefix of the list [l].
  *)
  let is_prefix_sublist ?(equal = Poly.equal) (prefix : 'a list) (li : 'a list) =
    let rec fx pre li =
      match (pre, li) with
      | [], [] -> true
      | _, [] -> false
      | [], _ :: _ -> true
      | hd :: tl, hd' :: tl' -> if equal hd hd' then fx tl tl' else false
    in
    if List.is_empty prefix then false else fx prefix li

  (**
      Returns the max of a list.
      /!\ The max of an empty list is min_int.
  *)
  let intlist_max li =
    List.fold_left ~f:(fun max elt -> if elt > max then elt else max) ~init:Int.min_value li

  (* Generate all k-length subslists of list l *)
  let k_combinations n lst =
    let rec inner acc k lst =
      match k with
      | 0 -> [ [] ]
      | _ -> (
          match lst with
          | [] -> acc
          | x :: xs ->
              let rec accmap acc f = function [] -> acc | x :: xs -> accmap (f x :: acc) f xs in
              let newacc = accmap acc (fun z -> x :: z) (inner [] (k - 1) xs) in
              inner newacc k xs)
    in
    inner [] n lst

  let last list = List.nth list (List.length list - 1)

  let rec lexicographic comp lx ly =
    match (lx, ly) with
    | [], [] -> 0
    | hd1 :: tl1, hd2 :: tl2 ->
        let x = comp hd1 hd2 in
        if x = 0 then lexicographic comp tl1 tl2 else x
    | _ :: _, [] -> 1
    | _ -> -1

  let lfst (l : ('a * 'b) list) : 'a list = List.map ~f:fst l

  let lmin score_func l =
    let scored_list = List.map ~f:(fun elt -> (score_func elt, elt)) l in
    let sorted_by_score =
      List.sort ~compare:(fun (s1, _) (s2, _) -> Poly.compare s1 s2) scored_list
    in
    match sorted_by_score with (_, elt) :: _ -> Some elt | _ -> None

  let lsnd (l : ('a * 'b) list) : 'b list = List.map ~f:snd l

  let lthird (l : ('a * 'b * 'c) list) : 'c list = List.map ~f:(fun (_, _, c) -> c) l

  let mapoption (f : 'a -> 'b option) (l : 'a list) : 'b list =
    List.map
      ~f:(function Some x -> x | _ -> failwith "x")
      (List.filter ~f:is_some (List.map ~f l))

  let mmax (measure : 'a -> int) (l : 'a list) =
    match l with
    | hd :: tl ->
        let f m e = if measure e > measure m then e else m in
        Some (List.fold ~f ~init:hd tl)
    | _ -> None

  let outer_join_lists (a, b) =
    List.fold_left
      ~f:(fun li i -> if List.mem li ~equal:Poly.equal i then li else i :: li)
      ~init:a b

  let prefixes l = List.mapi ~f:(fun i _ -> take l (i + 1)) l

  let rassoc ~equal (alist : ('a * 'b) list) (key : 'b) : 'a option =
    try Option.map ~f:fst (List.find ~f:(fun (_, y) -> equal y key) alist) with _ -> None

  let remove_elt ?(equal = Poly.equal) e l =
    let rec go l acc =
      match l with
      | [] -> rev acc
      | x :: xs when equal e x -> go xs acc
      | x :: xs -> go xs (x :: acc)
    in
    go l []

  let replace_ith (l : 'a list) (k : int) (e : 'a) =
    List.mapi ~f:(fun i e' -> if i = k then e else e') l

  let replace_last list elt = match List.rev list with _ :: t -> List.rev (elt :: t) | [] -> []

  let remove_duplicates l =
    let rec go l acc = match l with [] -> rev acc | x :: xs -> go (remove_elt x xs) (x :: acc) in
    go l []

  let remove_last list = match List.rev list with _ :: t -> List.rev t | [] -> []

  (**
     [remove_one l e] removes one occurrence of the element [e] in [l]. If such an element has been removed, then the functoin return the pair [true, l'] where [l'] is [l] minus one occurence of [e]. Otherwise the function returns [false, []].
  *)
  let remove_one ?(equal = Poly.equal) l e =
    let rec rem l =
      match l with
      | hd :: tl ->
          if equal hd e then (true, tl)
          else
            let b, ntl = rem tl in
            (b, hd :: ntl)
      | [] -> (false, [])
    in
    rem l

  (**
     [remove_prefix pre l] removes the prefix [pre] from the list [l]. If [pre] is a prefix of [l] then the returned value is [Some l'] where pre @ l' = l, otherwise the returned value is None.
  *)
  let rec remove_prefix ?(equal = Poly.equal) (prefix : 'a list) (list : 'a list) =
    match (prefix, list) with
    | [], [] -> Some []
    | _, [] -> None
    | [], l -> Some l
    | hd :: tl, hd' :: tl' -> if equal hd hd' then remove_prefix tl tl' else None

  (**
     [remove_intersection l1 l2] removes elements from [l1] and [l2] that are in both lists. It is {b not} equivalent to doing the same operation on thesets of element in l1 and l2. For example, if l1 contains two elements e and l2 only one e, then the first list of the pair returned will still contain an element e.
  *)
  let remove_intersection ?(equal = Poly.equal) l1 l2 : int list * int list =
    let f (nl1, nl2) l1e =
      let removed, nl2' = remove_one ~equal nl2 l1e in
      if removed then (nl1, nl2') else (nl1 @ [ l1e ], nl2')
    in
    List.fold ~f ~init:([], l2) l1

  let some_hd l = if length l > 0 then Some (hd l) else None

  let some_tl l = if length l > 0 then Some (tl l) else None

  let untriple a_b_c_li =
    List.fold_left a_b_c_li ~init:([], [], []) ~f:(fun (a_li, b_li, c_li) (a, b, c) ->
        (a_li @ [ a ], b_li @ [ b ], c_li @ [ c ]))
end

(**
  [timed f x] runs the function [f] and returns its results, along
  with a float equal to the time elapsed calling [f], measured using
  Unix.gettimeofday ().
*)
let timed f x =
  let t0 = Unix.gettimeofday () in
  let r = f x in
  (r, Unix.gettimeofday () -. t0)

(** Simple function to check if the argument is {e Some a}.
    @param ao some argument of type 'a option
    @return the object in the option
    @raise Failure if the argument is None
*)
let check_option ao = match ao with Some a -> a | None -> raise (Failure "check_option")

(** [somes l] returns the list of elements that are (Some _) in the list l,
    in the order they appear in the list l.
 *)
let somes l = List.map ~f:check_option (List.filter ~f:is_some l)

let ( =>> ) (f : 'a -> 'b option) (g : 'b -> 'c option) : 'a -> 'c option =
 fun x -> match f x with Some y -> g y | None -> None

let maybe_apply (f : 'a -> 'b) (v : 'a option) : 'b option =
  match v with Some a -> Some (f a) | None -> None

let maybe_apply_default (f : 'a -> 'b) (v : 'a option) (default : 'b) : 'b =
  match v with Some a -> f a | None -> default

let xorOpt o1 o2 =
  match (o1, o2) with
  | None, Some a -> Some a
  | Some _, Some _ -> raise (Failure "xorOpt")
  | _, _ -> None

let list_array_map f l = Array.to_list (Array.map ~f (Array.of_list l))

let rec count_map f l ctr =
  match l with
  | [] -> []
  | [ x ] -> [ f x ]
  | [ x; y ] ->
      (* order matters! *)
      let x' = f x in
      let y' = f y in
      [ x'; y' ]
  | [ x; y; z ] ->
      let x' = f x in
      let y' = f y in
      let z' = f z in
      [ x'; y'; z' ]
  | x :: y :: z :: w :: tl ->
      let x' = f x in
      let y' = f y in
      let z' = f z in
      let w' = f w in
      x' :: y' :: z' :: w' :: (if ctr > 500 then list_array_map f tl else count_map f tl (ctr + 1))

let list_map f l = count_map f l 0

let equals x1 x2 : bool = compare x1 x2 = 0

(* Pretty printing *)
let colon = Fmt.(fun f () -> pf f ":@ ")

let semicolon = Fmt.(fun f () -> pf f ";@ ")

let vert f () = Fmt.(if utf_8 f then pf f " 𒑰@;" else pf f "|@")

let arrow f () = Fmt.(if utf_8 f then pf f " →@;" else pf f "->@")

let wrap s = Fmt.(fun f () -> pf f s)

let string_msg msg s = Fmt.(fun f () -> pf f msg s)

let printer_msg msg pp e = Fmt.(fun f () -> pf f msg pp e)

let printer2_msg msg pp e pp2 e2 = Fmt.(fun f () -> pf f msg pp e pp2 e2)

let pp_map pp f m =
  let fl f (_, x) = pp f x in
  Fmt.((box ~indent:2 (braces (list ~sep:semicolon fl))) f (Map.to_alist m))

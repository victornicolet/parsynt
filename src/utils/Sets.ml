open Base

(** Set modules **)
module IntHash = struct
  type t = int

  let equal i j = i = j

  let hash i = i land Int.max_value
end

module IH = struct
  include Hashtbl.M (Int)

  let create (i : int) = Hashtbl.create (module Int) ~size:i

  let set (h : (int, 'a) Hashtbl.t) (key : int) (data : 'a) = Hashtbl.set h ~key ~data

  let add = set

  let find = Hashtbl.find_exn

  let iter f b = Hashtbl.iteri ~f:(fun ~key ~data -> f key data) b

  let mem h k = Hashtbl.mem h k

  let fold f h init = Hashtbl.fold h ~init ~f:(fun ~key ~data accum -> f key data accum)

  let add_all add_to bindings_to_add =
    iter (fun k v -> if mem add_to k then () else set add_to k v) bindings_to_add

  let add_list add_to (getk : 'a -> int) (l : 'a list) =
    List.iter ~f:(fun b -> add add_to (getk b) b) l

  let ih_join_left (newh : (int, 'a * 'b option) Hashtbl.t) (h1 : (int, 'a) Hashtbl.t)
      (h2 : (int, 'b) Hashtbl.t) : unit =
    Hashtbl.iteri h1 ~f:(fun ~key:k ~data:v1 ->
        match Hashtbl.find h2 k with
        | Some v2 -> set newh k (v1, Some v2)
        | None -> set newh k (v1, None))

  let iter_bottom_up h (isroot : 'a -> bool) (children : 'a -> 'a list) (app : 'a -> unit) : 'a list
      =
    let select_roots = fold (fun _ a roots -> if isroot a then a :: roots else roots) h [] in
    let rec build_botup stack acc =
      match stack with [] -> acc | hd :: tl -> build_botup (tl @ children hd) (hd :: acc)
    in
    let upbots = build_botup select_roots [] in
    List.iter ~f:app upbots;
    upbots

  let copy_into src dst = iter (fun key data -> Hashtbl.set dst ~key ~data) src
end

module IntegerMap = Map.M (Int)

(* Set of integers *)
module IS = struct
  include Set.M (Int)

  let empty = Set.empty (module Int)

  let singleton = Set.singleton (module Int)
end

module IM = struct
  include IntegerMap

  let add key data map = Map.add ~key ~data map

  let bindings = Map.to_alist

  let cardinal = Map.length

  let empty : 'v t = Map.empty (module Int)

  let filter f = Map.filteri ~f:(fun ~key ~data -> f key data)

  let find k m = Map.find_exn m k

  let fold f map init = Map.fold ~init ~f:(fun ~key ~data acc -> f key data acc) map

  let is_empty = Map.is_empty

  let iter f map = Map.iteri ~f:(fun ~key ~data -> f key data) map

  let map f map = Map.map ~f map

  let mapi f map = Map.mapi ~f:(fun ~key ~data -> f key data) map

  let mem i map = Map.mem map i

  let merge f a b =
    let f ~key = function
      | `Both (va, vb) -> f key (Some va) (Some vb)
      | `Left va -> f key (Some va) None
      | `Right vb -> f key None (Some vb)
    in
    Map.merge ~f a b

  let of_alist al = Map.of_alist_exn (module Int) al

  let set key data map = Map.set ~key ~data map

  let singleton (k : int) (i : 'a) : 'a t = Map.singleton (module Int) k i

  let keyset (imt : 'v t) : IS.t =
    Set.of_list (module Int) (List.map ~f:(fun (a, _) -> a) (Map.to_alist imt))

  let add_all (add_to : 'v t) (to_add : 'v t) : 'v t =
    Map.fold ~init:add_to to_add ~f:(fun ~key ~data mp ->
        if Map.mem add_to key then mp else Map.add_exn ~key ~data mp)

  let update_all (add_to : 'v t) (to_add : 'v t) : 'v t =
    Map.merge add_to to_add ~f:(fun ~key:_ valu ->
        match valu with `Both (_, vr) -> Some vr | `Left v -> Some v | `Right v -> Some v)

  let join_opt (map_a : 'v t) (map_b : 'v t) : 'v t =
    let f = Option.is_some in
    let a = Map.filter map_a ~f and b = Map.filter map_b ~f in
    add_all a b

  let inter (a : 'v t) (b : 'v t) : 'v t =
    let f ~key:_ data = match data with `Both (v1, _) -> Some v1 | `Left _ | `Right _ -> None in
    Map.merge ~f a b

  let is_disjoint ?(non_empty = fun _ _ -> true) (a : 'v t) (b : 'v t) : bool =
    try
      Map.fold ~init:true
        ~f:(fun ~key ~data bol ->
          if non_empty key data then if Map.mem a key then failwith "iom" else bol else bol)
        b
    with Failure _ -> false

  let disjoint_sets (im1 : 'v t) (im2 : 'v t) : 'v t * 'v t * 'v t * 'v t =
    let im1_in_im2 =
      Map.fold
        ~init:(Map.empty (module Int))
        ~f:(fun ~key ~data mmap -> if Map.mem im2 key then Map.add_exn ~key ~data mmap else mmap)
        im1
    in
    let im2_in_im1 =
      Map.fold ~init:im1
        ~f:(fun ~key ~data map -> if Map.mem im1 key then Map.add_exn ~key ~data map else map)
        im2
    in
    let im1_only =
      Map.fold
        ~init:(Map.empty (module Int))
        ~f:(fun ~key ~data map -> if Map.mem im2 key then map else Map.add_exn ~key ~data map)
        im1
    in
    let im2_only =
      Map.fold
        ~init:(Map.empty (module Int))
        ~f:(fun ~key ~data map -> if Map.mem im1 key then map else Map.add_exn ~key ~data map)
        im2
    in
    (im1_in_im2, im2_in_im1, im1_only, im2_only)

  let of_ih (ih : 'v IH.t) : 'v t =
    Hashtbl.fold ih ~init:empty ~f:(fun ~key ~data m -> Map.add_exn ~key ~data m)

  let to_alist (im : 'v t) : (int * 'v) list = Map.to_alist ~key_order:`Decreasing im

  let of_alist_dup (im : (int * 'v) list) : [ `Duplicate_key of int | `Ok of 'v t ] =
    Map.of_alist (module Int) im
end

(*  Strings *)

module SH = struct
  include Hashtbl.M (String)

  let create (size : int) : 'v t = Hashtbl.create ~size (module String)

  let add (table : 'v t) (key : string) (data : 'v) : unit =
    match Hashtbl.add table ~key ~data with _ -> ()

  let set (table : 'v t) (key : string) (data : 'v) : unit = Hashtbl.set table ~key ~data

  let clear (table : 'v t) = Hashtbl.clear table

  let mem (table : 'v t) (s : string) = Hashtbl.mem table s

  let iter f (table : 'v t) = Hashtbl.iteri table ~f:(fun ~key ~data -> f key data)

  let find (table : 'v t) (s : string) = Hashtbl.find_exn table s

  let replace (table : 'v t) (s : string) v = Hashtbl.set table ~key:s ~data:v

  let fold (f : string -> 'v -> 'a -> 'a) (table : 'v t) (init : 'a) : 'a =
    Hashtbl.fold table ~init ~f:(fun ~key ~data accum -> f key data accum)
end

module SM = struct
  include Map.M (String)

  let empty = Map.empty (module String)

  let singleton i = Map.singleton (module String) i

  let add key data m = Map.set ~key ~data m

  let set = add

  let find k m = Map.find m k

  let from_bindings (b : (string * 'a) list) : 'a t =
    List.fold ~f:(fun smap (key, data) -> Map.set smap ~key ~data) ~init:empty b
end

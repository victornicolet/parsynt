module S = Str
module IOS = Reachingdefs.IOS


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

(* Set of integers *)
module IS =
struct
  include Set.Make (struct
      type t = int
      let compare = Pervasives.compare
    end)


  let purified ioset =
    IOS.fold (fun io is ->
        match io with
        | Some i -> add i is
        | None -> is) ioset empty
end

module SM = struct
  include Map.Make(String)
  let update map key nval update =
    try
      let pval = find key map in
      add key (update pval nval) map
    with Not_found ->
      add key nval map

  let from_bindings (b : (string * 'a) list) : 'a t =
    List.fold_left
      (fun smap (k,v) -> add k v smap) empty b
end


module VSo = Usedef.VS

module SH = Hashtbl.Make (struct
    type t = String.t
    type key = String.t
    let equal s1 s2 = s1 = s2
    let hash s = Hashtbl.hash s
  end)

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

  let join_opt map_a map_b =
    let f k a = match a with Some x -> true | None -> false in
    let a = filter f map_a in
    let b = filter f map_b in
    add_all a b


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

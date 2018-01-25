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

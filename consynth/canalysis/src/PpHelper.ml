open Printf
open Format

module SH = Map.Make(String)

let colorPrefix = "\x1b"

let colormap = 
  List.fold_left2
    (fun m k v -> SH.add k (colorPrefix^v) m)
    SH.empty
    ["black"; "red"; "green"; "yellow"; "blue"]
    ["[30m"; "[31m"; "[32m"; "[33m"; "[34m"]

let color cname =
  try
    SH.find cname colormap
  with Not_found -> colorPrefix^"[0m"

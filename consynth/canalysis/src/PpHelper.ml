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

let default = colorPrefix^"[0m"

let rec ppli ppf pfun =
  function
  | hd :: tl -> fprintf ppf "%a;%a" pfun hd (fun fmt -> ppli fmt pfun) tl
  | [] -> fprintf ppf "%s" ""

(**TODO : replace characters that are srtting colro back to default in incoming
   string *)
let printerr s =
  Format.fprintf err_formatter "%s%s%s" (color "red") s default

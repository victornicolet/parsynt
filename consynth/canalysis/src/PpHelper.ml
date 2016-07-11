open Printf
open Format
open Utils

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

(** Map printing *)
let ppimap
    (pelt : formatter -> 'a -> unit)
    (ppf : formatter) : 'a IM.t -> unit =
  IM.iter
    (fun i a ->
      fprintf ppf "@[<hov 2> %i -> %a@]@;" i pelt a)



let string_of_loc (loc : Cil.location) =
 sprintf "<#line %i in %s>" loc.Cil.line loc.Cil.file


(**TODO : replace characters that are srtting colro back to default in incoming
   string *)
let printerr s =
  Format.fprintf err_formatter "%s%s%s" (color "red") s default

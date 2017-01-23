open Printf
open Format
open Utils


let colorPrefix = "\x1b"

let colormap =
  List.fold_left2
    (fun m k v -> SM.add k (colorPrefix^v) m)
    SM.empty
    ["black"; "red"; "green"; "yellow"; "blue"; "violet"; "cyan"; "white";
     "i"; "u"; "b"; "grey";
     "b-grey"; "b-red"; "b-green"; "b-yellow";"b-blue"; "b-violet"; "b-cyan"; "b-white"]
    ["[30m"; "[31m"; "[32m"; "[33m"; "[34m"; "[35m"; "[36m"; "[37m";
     "[3m"; "[4m"; "[1m"; "[2m";
     "[100m"; "[101m"; "[102m"; "[103m";"[104m"; "[105m"; "[106m"; "[107m"]

let color cname =
  try
    SM.find cname colormap
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

let pp_string_list fmt =
  ppli fmt ~sep:" " (fun fmt s -> fprintf fmt "%s" s)

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


(**TODO : replace characters that are setting color back to default in incoming
   string *)
let printerr s =
  Format.fprintf err_formatter "%s%s%s" (color "red") s default

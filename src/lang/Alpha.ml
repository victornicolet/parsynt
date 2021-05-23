open Base
open Utils

let _NID = ref 0;;
let _VID = ref 99;;
let names : int SH.t = SH.create 0;;

let reserved =
  [ "INT_MIN"; "INT_MAX"; "INT"; "max"; "min"; "+"; "-"; "*"; "/"; "=";
    ">"; ">="; "<="; "=="; "=";
    "exp"; "expt"; "log";
    "bool"; "int"; "float"; "real"; "bitvector";
    "list"; "map"; "fold"; "zip"; "range"
  ]


let init () =
  _NID := 0;
  (* Special variables - ids from 0 to 99 *)
  SH.clear names;
  List.iter ~f:(fun s -> SH.add names s !_NID; Int.incr _NID) reserved
;;

let _NI = ref 0;;

let rec get_new_name ?(suffix = "") (base : string)  =
  let bn = base^suffix in
  if SH.mem names bn then
    begin
      Int.incr _NI;
      Int.incr _NID;
      get_new_name ~suffix:(Int.to_string !_NI) base
    end
  else
    begin
      SH.add names bn !_NID;
      _NI := 0;
      bn
    end

let get_new_id () = Int.incr _VID; !_VID

let add_name (n : string) =
  let nid = get_new_id () in
  SH.add names n nid

open Base
open Alpha
open Typ
open Utils

let _names : (string * typ) list SH.t = SH.create 10

let _saved_names : (string * typ) list SH.t = SH.create 10

let save () =
  let f ~key ~data = Hashtbl.set _saved_names ~key ~data in
  Hashtbl.iteri _names ~f

let restore () =
  let f ~key ~data = Hashtbl.set _names ~key ~data in
  Hashtbl.iteri _saved_names ~f

let get (sname : string) : typ option =
  Option.(Hashtbl.find _names sname >>| fun fields -> TStruct (sname, fields))

let add_name (sname : string) (fields : (string * typ) list) =
  Alpha.add_name sname;
  SH.set _names sname fields

let type_of_fields (memt : (string * typ) list) : typ option =
  Hashtbl.fold ~init:None
    ~f:(fun ~key ~data acc ->
      if struct_fields_equal data memt then Some (TStruct (key, memt)) else acc)
    _names

let decl_anonymous (memt : (string * typ) list) =
  match type_of_fields memt with Some _ -> () | None -> add_name (get_new_name "$") memt

let decl_of_vars (memt : (string * typ) list) : string =
  match type_of_fields memt with
  | Some (TStruct (s, _)) -> s
  | _ ->
      let new_name = get_new_name "$" in
      add_name new_name memt;
      new_name

let is_anonymous (t : typ) : bool =
  match t with TStruct (key, _) -> String.is_prefix key ~prefix:"$" | _ -> false

let name_of_fields (fieldt : (string * typ) list) : string option =
  Hashtbl.fold ~init:None
    ~f:(fun ~key ~data acc -> if struct_fields_equal fieldt data then Some key else acc)
    _names

let field_type (sname : string) (fieldname : string) : typ option =
  O.(
    Hashtbl.find _names sname >>= fun fields -> List.Assoc.find fields ~equal:String.equal fieldname)

let is_struct_type = function TStruct _ -> true | _ -> false

let dump_state () =
  Hashtbl.iteri _names ~f:(fun ~key ~data ->
      Fmt.(
        pf stdout "@[> Struct : %s : %a@]@." key
          (list ~sep:semicolon (pair ~sep:sp string pp_typ))
          data))

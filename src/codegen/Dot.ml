open Utils
open Base

type edge = int * int

type id = string

class dotgraph = object
  val mutable directed_graph = true
  val mutable num_nodes = 0
  val nodes : id IH.t = Hashtbl.create (module Int)
  val node_ids : int SH.t = Hashtbl.create (module String)
  val edges : int IH.t = Hashtbl.create (module Int)
  val nodelabels : string IH.t = Hashtbl.create (module Int)
  val mutable graphname = "graphname"

  method add_node ?(label = None) (nid : id) =
    num_nodes <- num_nodes + 1;
    Hashtbl.add_exn node_ids ~key:nid ~data:num_nodes;
    Hashtbl.add_exn nodes ~key:num_nodes ~data:nid;
    match label with
    | None -> ()
    | Some s -> Hashtbl.add_exn nodelabels ~key:num_nodes ~data:s


  method add_edge (orig : id) (dest : id) =
    let orig_id = Hashtbl.find node_ids orig in
    let dest_id = Hashtbl.find node_ids dest in
    match orig_id, dest_id with
    | Some oid, Some did -> Hashtbl.add_exn edges ~key:oid ~data:did
    | _ , _ -> ()

  method pp_graph (frmt : Formatter.t) =
    let link = if directed_graph then "->" else "--" in
    (if directed_graph then
       Fmt.(pf frmt "digraph %s {@." graphname)
     else
       Fmt.(pf frmt "graph %s {@." graphname));
    Hashtbl.iteri nodelabels
      ~f:(fun ~key:node_id ~data:label ->
          Fmt.(pf frmt "\t%a [label=\"%s\"];"
                 (option string) (Hashtbl.find nodes node_id) label));

    Hashtbl.iteri edges
      ~f:(fun ~key:orig_id ~data:dest_id ->
          Fmt.(pf frmt "\t%a %s %a;@."
                 (option string) (Hashtbl.find nodes orig_id) link
                 (option string) (Hashtbl.find nodes dest_id)));
    Fmt.(pf frmt "}@.")
end

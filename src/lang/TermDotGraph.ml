open Codegen.Dot
open Base
open Typ
open Term
open TermPp

(* Generate dotgraph *)

let fill_graph (d : dotgraph) (t : term) =
  let ic = ref 0 in
  let marked_node sexp =
    Int.incr ic;
    let label = string_of_sexp sexp in
    (label ^ "_" ^ Int.to_string !ic, label)
  in
  let var_node v =
    Int.incr ic;
    match v with Var v -> (v.vname ^ "_" ^ Int.to_string !ic, Some v.vname)
  in
  let rnode = "root" in
  d#add_node "root";
  let rec fill incoming trm =
    match trm.texpr with
    | EBin (b, e1, e2) ->
        let bnode, lbl = marked_node (Binop.sexp_of_t b) in
        d#add_node ~label:(Some lbl) bnode;
        d#add_edge incoming bnode;
        fill bnode e1;
        fill bnode e2
    | EWith (s, n, b) ->
        let bnode, lbl = marked_node (sexp_of_string n) in
        d#add_node ~label:(Some lbl) bnode;
        d#add_edge incoming bnode;
        fill bnode s;
        fill bnode b
    | EConst _ ->
        Int.incr ic;
        let cst, lab =
          ( Fmt.(to_to_string (fun f () -> pf f "\"%a #(%i)\"" pp_term t !ic) ()),
            Fmt.(to_to_string pp_term t) )
        in
        d#add_node ~label:(Some lab) cst;
        d#add_edge incoming cst
    | EEmpty ->
        let cst = "empty" in
        d#add_node ~label:(Some "empty") cst;
        d#add_edge incoming cst
    | EIte (c, e1, e2) ->
        let bnode, _ = marked_node (sexp_of_string "ite") in
        d#add_node ~label:(Some "ite") bnode;
        d#add_edge incoming bnode;
        fill bnode c;
        fill bnode e1;
        fill bnode e2
    | ESetL (a, i, e) ->
        let bnode, _ = marked_node (sexp_of_string "set") in
        d#add_node ~label:(Some "set") bnode;
        d#add_edge incoming bnode;
        fill bnode a;
        fill bnode i;
        fill bnode e
    | EUn (u, e) ->
        let unode, ul = marked_node (Unop.sexp_of_t u) in
        d#add_node ~label:(Some ul) unode;
        d#add_edge incoming unode;
        fill unode e
    | EVar lhv ->
        let vnode, lv = var_node lhv in
        d#add_node ~label:lv vnode;
        d#add_edge incoming vnode
    | EHole _ ->
        let vnode, lv = marked_node (sexp_of_string "??") in
        d#add_node ~label:(Some lv) vnode;
        d#add_edge incoming vnode
    | ETuple el ->
        let bnode, _ = marked_node (sexp_of_string "Tuple") in
        d#add_node ~label:(Some "tuple") bnode;
        d#add_edge incoming bnode;
        List.iter ~f:(fill bnode) el
    | EStruct mems ->
        let bnode, _ = marked_node (sexp_of_string "Struct") in
        d#add_node ~label:(Some "struct") bnode;
        d#add_edge incoming bnode;
        List.iter ~f:(fun (_, t) -> fill bnode t) mems
    | EList el ->
        let bnode, _ = marked_node (sexp_of_string "List") in
        d#add_node ~label:(Some "list") bnode;
        d#add_edge incoming bnode;
        List.iter ~f:(fill bnode) el
    | EChoice el ->
        let bnode, _ = marked_node (sexp_of_string "Choice") in
        d#add_node ~label:(Some "choose") bnode;
        d#add_edge incoming bnode;
        List.iter ~f:(fill bnode) el
    | EMem (e, i) ->
        let bnode, _ = marked_node (sexp_of_string "Mem") in
        let inode, il = marked_node (sexp_of_int i) in
        d#add_node ~label:(Some "mem") bnode;
        d#add_edge incoming bnode;
        fill incoming e;
        d#add_node ~label:(Some il) inode;
        d#add_edge bnode inode
    | EMemStruct (sname, fieldname, t) ->
        let bnode, _ = marked_node (sexp_of_string (sname ^ "-mem")) in
        let inode, il = marked_node (sexp_of_string fieldname) in
        d#add_node ~label:(Some (sname ^ "-field")) bnode;
        d#add_edge incoming bnode;
        fill incoming t;
        d#add_node ~label:(Some il) inode;
        d#add_edge bnode inode
    | ELambda (vl, e) ->
        let bnode, _ = marked_node (sexp_of_string "lam") in
        d#add_node ~label:(Some "lam") bnode;
        d#add_edge incoming bnode;
        List.iter
          ~f:(fun v ->
            let vnode, l = marked_node (sexp_of_string v.vname) in
            d#add_node ~label:(Some l) vnode;
            d#add_edge bnode bnode)
          vl;
        fill bnode e
    | EFoldL (f, ei, le) ->
        let bnode, _ = marked_node (sexp_of_string "FoldL") in
        d#add_node bnode;
        d#add_edge incoming bnode;
        fill bnode f;
        fill bnode ei;
        fill bnode le
    | EFoldR (f, ei, le) ->
        let bnode, _ = marked_node (sexp_of_string "FoldR") in
        d#add_node bnode;
        d#add_edge incoming bnode;
        fill bnode f;
        fill bnode ei;
        fill bnode le
    | EApp (f, el) ->
        let bnode, _ = marked_node (sexp_of_string "App") in
        d#add_node bnode;
        d#add_edge incoming bnode;
        fill bnode f;
        List.iter ~f:(fill bnode) el
    | ELet (v, e, e') ->
        let bnode, _ = marked_node (sexp_of_string "Let") in
        let enode, _ = marked_node (sexp_of_string "=") in
        let vnode, lv = var_node v in
        d#add_node bnode;
        d#add_edge incoming bnode;
        d#add_node enode;
        d#add_edge bnode enode;
        d#add_node ~label:lv vnode;
        d#add_edge enode vnode;
        fill enode e;
        fill bnode e'
    | ELetValues _ -> failwith "TODO implement let-values in dotgraph"
    | EPLet _ -> failwith "TODO implement parallel bindings in dotgraph"
  in
  fill rnode t

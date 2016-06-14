(** 
    Custom dataflow analysis not provided by Cil.
    Main components :
    - Read/Write set of a body
*)
open Hashtbl
open String
open Cil

module DF = Dataflow
module IH = Inthash

module ReadWriteSet =
struct
  let name = "Read/Write Set"

  let debug = ref false

  (** 
      Read/ write sets are encoded as a integer hash where 
      keys are variables IDs and the stored elements are the 
      information on the set it belongs to.
  *)
  let wvar = 1
  let rvar = 0
  let rwvar = 2

  type t = (int IH.t)
    
  let copy vmap = IH.copy vmap

  (** Additional operations on IH *)
  let combine v1 v2 =
    if v1 == v2 then v1 else rwvar

  let replaceIn hmap k v =
    try
      let vpre = IH.find hmap k in
      IH.replace hmap k (combine vpre v)
    with
    | Not_found -> IH.add hmap k v

  let addvar hmap cvar v =
    match cvar with
    | (Cil.Var vi, _) -> 
       replaceIn hmap vi.vid v
    | _ -> raise (Failure "Works only with lvalues that are variables")

  (** Combining two  sets is simply adding all the bindings of the second one
      int the new one, following he rule combine for two bindings *)
  let combs hmap1 hmap2 =
    IH.iter (replaceIn hmap1) hmap2; hmap1

  let eqs hmap1 hmap2 =
    IH.fold 
      (fun k v b ->
        try b && (v == IH.find hmap2 k)
        with Not_found -> false
      )
      hmap1 true

  (** 
      We also need to inspect the expressions and look at what variables are
      read inside the right-hand side expressions
  *)
       
  (** Modify the variable information inside m *)
  let used_in_epxr expr m = 
    let rec aux e =
      begin
        match e with
        | Lval lv -> addvar m lv rvar
        | SizeOfE e -> aux e
        | AlignOfE e -> aux e
        | UnOp (_ , e1, _) -> aux e1
        | BinOp (_, e1, e2, _) -> aux e1; aux e2
        | Question (e1, e2, e3, _) -> aux e1; aux e2; aux e3
        | CastE (_, e) -> aux e
        | _ -> ()
      end
    in
    aux expr

  (** 
      Now the transfer functions used in the dataflow ramework while inspecting
      the program
  *)
  let stmtStartData = IH.create 32

  (** TODO  : pretty printing function *)
  let pretty () m = Pretty.line

  let computeFirstPredecessor stm m =
    m

  let combinePredecessors (stm: Cil.stmt) ~(old:t) (m:t) =
    if (eqs old m) then None else Some (combs old m)

    

  let doInstr (inst : Cil.instr) (m : t) =
    let transf (m : t) =
      match inst with
      | Set (lv, e, _) ->
         begin
           addvar m lv wvar;
           used_in_expr e m;
           m
         end
      | Call (lvo, ef, eargs, _) ->
         begin
           match lvo with 
           | Some lv -> addvar m lv wvar; m
           | None -> m
         end;
      | _ -> m
    in
    DF.Post transf
      
  let doStmt (stmt : Cil.stmt) (m : t) = DF.SDefault

  let doGuard (condition : Cil.exp) _ = DF.GDefault

  let filterStmt (stm : Cil.stmt) = true
    
end

module WR = DF.ForwardsDataFlow (ReadWriteSet)

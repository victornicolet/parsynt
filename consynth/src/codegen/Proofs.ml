open Utils
open SketchTypes
open Cil


(* Conf variables :
   - Suffix for the Join : dafny_join_suffix
   - Prefix for the homorphism : dafny_hom_prefix
   - Assertion for empty list in homomorphism: dafny_hom_empty_assert
 *)
type proofVariable =
  {
    name : string;
    empty_value : constants;
    function_expr : skExpr;
    join_expr : skExpr;
    depends : proofVariable list;
  }

let find_function_expr vi solved_sketch = ()


let find_join_expr vi solved_sketch = ()


let genProofVariables solved_sketch =

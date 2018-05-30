open Beta

open FuncTypes
exception VariableDiscoveryError of string
val max_exec_no : int ref
val debug : bool ref
val debug_dev : bool ref
val verbose : bool ref
val discover : prob_rep -> prob_rep

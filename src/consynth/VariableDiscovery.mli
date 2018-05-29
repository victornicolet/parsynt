open Beta

open FuncTypes
exception VariableDiscoveryError of string
val debug : bool ref
val debug_dev : bool ref
val verbose : bool ref
val discover : prob_rep -> prob_rep

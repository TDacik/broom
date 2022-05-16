(* Use #use "Load_all.ml" in utop *)

#mod_use "Formula.ml"
#require "z3"
#mod_use "Z3wrapper.ml"
#mod_use "Abduction.ml"
#mod_use "State.ml"
#mod_use "Contract.ml"

open Z3
open Z3wrapper
let cfg = [("model", "true"); ("proof", "false")]
let ctx = (mk_context cfg)
let solv = (Solver.mk_solver ctx None)
let z3_names=get_sl_functions_z3 ctx



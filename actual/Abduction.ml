(* in Utop use 
	#mod_use "Formula.ml" 
   	#require "z3" 
	#mode_use "Z3_wrapper"
*)

open Formula
open Z3
open Z3wrapper


let match1 ctx solv z3_names form1 i1 form2 i2 =
	let lhs = 
		match (List.nth form1.sigma i1) with 
		| Hpointsto (a, _) -> (expr_to_solver ctx z3_names a)
	in
	let rhs = 
		match (List.nth form2.sigma i2) with 
		| Hpointsto (a, _) -> (expr_to_solver ctx z3_names a)
	in

	let query = Boolean.mk_not ctx (Boolean.mk_eq ctx lhs rhs) ::
		(List.append (formula_to_solver ctx form1) (formula_to_solver ctx form2))
	in
	(Solver.check solv query)=UNSATISFIABLE



(*  Experiments
let names_z3=get_sl_functions_z3 ctx in
match1 ctx solv names_z3 form1 0 pre_free 0

*)


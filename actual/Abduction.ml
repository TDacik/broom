(* in Utop use 
	#mod_use "Formula.ml" 
   	#require "z3" 
	#mod_use "Z3wrapper.ml"
*)

open Formula
open Z3
open Z3wrapper


(**** MATCH 1 ****)

(* Check whether match1 can be applied on i1^th pointsto on LHS and i2^th points-to on RHS *)
let check_match1 ctx solv z3_names form1 i1 form2 i2 =
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

(* Find pair of points-to for match1. Return (-1,-1) if unposibble *) 
let rec find_match1_ll ctx solv z3_names form1 i1 form2 =
	let rec try_with_rhs i2 =
		if (List.length form2.sigma) <= i2 
		then -1
		else (if (check_match1 ctx solv z3_names form1 i1 form2 i2) 
			then i2
			else -1)
	in
	if (List.length form1.sigma) <= i1 
	then (-1,-1)
	else
		match (try_with_rhs 0) with
		| -1 -> (find_match1_ll ctx solv z3_names form1 (i1+1) form2)
		| x -> (i1,x) 

let find_match1 ctx solv z3_names form1 form2 =
	find_match1_ll ctx solv z3_names form1 0 form2


(* apply the match1 rule to i=(i1,i2)---i1^th pointsto on LHS and i2^th points-to on RHS,
   find_match1 must be used
*)
let apply_match1 i form1 form2 =
	let nequiv a b = not (a=b) in
	let remove k form =
		{ pi=form.pi;
		  sigma=List.filter (nequiv (List.nth form.sigma k)) form.sigma }
	in
	match i with
	| (i1,i2) ->
		(remove i1 form1), (remove i2 form2)
		

(*  Experiments
let names_z3=get_sl_functions_z3 ctx in
check_match1 ctx solv names_z3 form1 0 pre_free 0

find_match1_ll ctx solv names_z3 form1 0 pre_free

*)


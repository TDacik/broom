open Formula
open Z3
open Z3wrapper

type res =
| AbstractionApply of Formula.t
| AbstractionFail

(* for a given pointsto a1 -> _ get indexes of all other pointsto with an equal base adress 
  The pointsto is provided by index "i1" to the list form.sigma
*) 

let rec get_eq_base ctx solv z3_names form i1 index =
	if index=(List.length form.sigma) then []
	else
	let ff = Boolean.mk_false ctx in
	let a1 = match (List.nth form.sigma i1) with
		| Slseg _ -> ff
		| Hpointsto (a,_,_) -> (expr_to_solver ctx z3_names a)
	in
	let a2 = match (List.nth form.sigma index) with
		| Slseg _ -> ff
		| Hpointsto (a,_,_) -> (expr_to_solver ctx z3_names a)
	in
	if (a2=ff)||(i1=index) then (get_eq_base ctx solv z3_names form i1 (index+1))
	else
		(* form -> base(a1) = base(a2) *)
		let query=[ (Boolean.mk_and ctx (formula_to_solver ctx form));
			(Boolean.mk_not ctx (Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [a1]) (Expr.mk_app ctx z3_names.base [a2])))
		] in
		if (Solver.check solv query)=UNSATISFIABLE then index :: (get_eq_base ctx solv z3_names form i1 (index+1))
		else  (get_eq_base ctx solv z3_names form i1 (index+1))


let try_pointsto_to_lseg ctx solv z3_names form i1 i2 =
(* try to abstract two pointsto predicates into a list segment *)
	let ff = Boolean.mk_false ctx in
	let a1,l1,b1 = match (List.nth form.sigma i1) with
		| Slseg _ -> ff,ff,ff
		| Hpointsto (a,l,b) -> (expr_to_solver ctx z3_names a),(expr_to_solver ctx z3_names l),(expr_to_solver ctx z3_names b)
	in
	let a2,l2,b2 = match (List.nth form.sigma i2) with
		| Slseg _ -> ff,ff,ff
		| Hpointsto (a,l,b) -> (expr_to_solver ctx z3_names a),(expr_to_solver ctx z3_names l),(expr_to_solver ctx z3_names b)
	in
	 (* Slseg can not match the condition *)
	if ((a1=ff) || (a2=ff)) then false
	else
	(* First do a base check --- i.e. query1 + query2 *)
	(* form -> base(a1) != base(a2) /\ l1 = l2 /\ base(b1) = base(a2) *)
	let query1 = [	(Boolean.mk_and ctx (formula_to_solver ctx form));
		Boolean.mk_or ctx [
			(Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [a1]) (Expr.mk_app ctx z3_names.base [a2]));
			(Boolean.mk_not ctx (Boolean.mk_eq ctx l1 l2));
			(Boolean.mk_not ctx (Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [b1]) (Expr.mk_app ctx z3_names.base [a2])))]
	] in
	(* SAT: form /\ a1-base(a1) = a2 - base(a2) *)
	let query2 = [ (Boolean.mk_and ctx (formula_to_solver ctx form));
		Boolean.mk_eq ctx 
			(Arithmetic.mk_sub ctx [ a1; (Expr.mk_app ctx z3_names.base [a1]) ])
			(Arithmetic.mk_sub ctx [ a2; (Expr.mk_app ctx z3_names.base [a2]) ])
	] in
	if not (((Solver.check solv query1)=UNSATISFIABLE)&& ((Solver.check solv query2)=SATISFIABLE)) then false
	else
	(* check all pointsto with equal bases to a1/a2 *)
	let a1_block=get_eq_base ctx solv z3_names form i1 0 in
	let a2_block=get_eq_base ctx solv z3_names form i2 0 in
	(List.length a1_block) = (List.length a2_block)





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


(* Check that points-to on i1 and i2 can have (=SAT) equal distance from base of the block *)
let check_eq_dist_from_base ctx solv z3_names form i1 i2 =
	let ff = Boolean.mk_false ctx in
	let a1 = match (List.nth form.sigma i1) with
		| Slseg _ -> ff
		| Hpointsto (a,_,_) -> (expr_to_solver ctx z3_names a)
	in
	let a2 = match (List.nth form.sigma i2) with
		| Slseg _ -> ff
		| Hpointsto (a,_,_) -> (expr_to_solver ctx z3_names a)
	in
	if ((a1=ff) || (a2=ff)) then false
	else
	(* SAT: form /\ a1-base(a1) = a2 - base(a2) *)
	let query2 = [ (Boolean.mk_and ctx (formula_to_solver ctx form));
		Boolean.mk_eq ctx 
			(Arithmetic.mk_sub ctx [ a1; (Expr.mk_app ctx z3_names.base [a1]) ])
			(Arithmetic.mk_sub ctx [ a2; (Expr.mk_app ctx z3_names.base [a2]) ])
	] in
	((Solver.check solv query2)=SATISFIABLE)


(* The input is a formula and two lists of indexes to form.sigma,
  the goal is to create a list of tuples (a,b) such that pointsto predicates on position a and b has equal distance from 
  base of particular blocks *)
type match_res =
| MatchOK of (int * int) list
| MatchFail



let rec match_pointsto_from_two_blocks ctx solv z3_names form l1 l2 =
	match l1 with
	| [] -> if l2=[] then MatchOK [] else MatchFail
	| i1::l1_rest ->
		let rec find_second l2_tmp =
			match l2_tmp with
			| [] -> -1
			| f::r -> 
				if (check_eq_dist_from_base ctx solv z3_names form i1 f) then f
				else find_second r
		in
	let i2=find_second l2 in
	if i2=(-1) then MatchFail
	else
		let neg_i2 a = not (a=i2) in
		let l2_rest=List.filter neg_i2 l2 in
		let rest=match_pointsto_from_two_blocks ctx solv z3_names form l1_rest l2_rest in
		match rest with
		| MatchFail -> MatchFail
		| MatchOK a -> MatchOK ((i1,i2) :: a)

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

(***** Experiments *****)
let form_abstr1 = {
    sigma = [ Hpointsto (Var 1,ptr_size, Var 2); Hpointsto(BinOp ( Pplus, Var 1, ptr_size),ptr_size, Var 10);
    	Hpointsto (Var 2,ptr_size, Var 3); Hpointsto (BinOp ( Pplus, Var 2, ptr_size),ptr_size, Var 10)];
    pi = [ BinOp ( Peq, Var 1, UnOp ( Base, Var 1));
        BinOp ( Peq, Var 2, UnOp ( Base, Var 2))
        ]
    (*evars = [ 2;3;4 ]*)
}




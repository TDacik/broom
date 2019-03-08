(* in Utop use 
	#mod_use "Formula.ml" 
   	#require "z3" 
	#mod_use "Z3wrapper.ml"
*)

open Formula
open Z3
open Z3wrapper

(** result of the rule application
    form1 * form2 * M
    or Fail
**)
type res =
| Apply of Formula.t * Formula.t * Formula.t
| Fail

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


(* apply the match rule to i=(i1,i2)---i1^th pointsto on LHS and i2^th points-to on RHS,
   find_match1 must be used
*)
let apply_match i form1 form2 =
	let nequiv a b = not (a=b) in
	let remove k form =
		{ pi=form.pi;
		  sigma=List.filter (nequiv (List.nth form.sigma k)) form.sigma }
	in
	match i with
	| (i1,i2) ->
		(remove i1 form1), (remove i2 form2)
		

(* Try to apply match1 rule. The result is:
	form1 - the LHS formula with removed matched part and added equality x=y
	form2 - the RHS formula with removed matched part
	M - the empty learned part
*)
let try_match1 ctx solv z3_names form1 form2 =
	let m=find_match1 ctx solv z3_names form1 form2 in
	match m with
	| (-1,-1) -> Fail
	| (i1,i2) ->
		let (f1,f2)=apply_match (i1,i2) form1 form2 in
		let y1=match (List.nth form1.sigma i1) with 
			| Hpointsto (_, a) -> a in
		let y2=match (List.nth form2.sigma i2) with 
			| Hpointsto (_, a) -> a in
		(* There is a problem in the cases, where one of the y1/y2 is Undef,
		   We haveprobably to treat Undef in the solver as uninterpreted values *)
		Apply ( { sigma=f1.sigma; pi = (BinOp ( Peq, y1,y2))::f1.pi},
			f2, 
			{sigma=[]; pi=[]})

(**** LEARN 1 ****)

(* let x be: form2.sigma[i2]=x->_ 
  we know that x!= y for all y->_ \in form1.sigma
  now find a z->_ in form1.sigma such that base(z) = base(x) is valid *)
let rec find_z ctx solv z3_names form1 z form2 i2 =
	if (List.length form1.sigma) <= z
		then -1
	else
	let rhs = 
		match (List.nth form2.sigma i2) with 
		| Hpointsto (a, _) -> (expr_to_solver ctx z3_names a)
	in
	let lhs = 
		match (List.nth form1.sigma z) with 
		| Hpointsto (a, _) -> (expr_to_solver ctx z3_names a)
	in
	let query = Boolean.mk_not ctx (
		Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [lhs]) (Expr.mk_app ctx z3_names.base [rhs])) ::
		(List.append (formula_to_solver ctx form1) (formula_to_solver ctx form2))
	in
	if (Solver.check solv query)=UNSATISFIABLE then z
	else find_z ctx solv z3_names form1 (z+1) form2 i2
	
(* check whether we can apply learn1 on the form2.sigma[i2].
   The result is -1: imposible
   		 0...k: the index of "z"
*)
let check_learn1 ctx solv z3_names form1 form2 i2 =
	let rhs = 
		match (List.nth form2.sigma i2) with 
		| Hpointsto (a, _) -> (expr_to_solver ctx z3_names a)
	in
	(* create list of equalities between form2.sigma[i2] and all items in form1.sigma *)
	let rec list_eq pointsto_list =
		match pointsto_list with
		| [] -> []
		| first::rest ->
			(Boolean.mk_eq ctx rhs 
				( match first with 
					| Hpointsto (a, _) -> (expr_to_solver ctx z3_names a))
			)
			:: list_eq rest
	in
	(* problem if form1.sigma is empty list .... to be solved *)
	let query1 = match (list_eq form1.sigma) with
		| [] -> List.append (formula_to_solver ctx form1) (formula_to_solver ctx form2)
		| a -> (Boolean.mk_or ctx (list_eq form1.sigma))
			::
			(List.append (formula_to_solver ctx form1) (formula_to_solver ctx form2))
	in
	if (Solver.check solv query1)=UNSATISFIABLE then
		find_z ctx solv z3_names form1 0 form2 i2	
	else -1
		

(* try to apply learn1 rule *)
let try_learn1 ctx solv z3_names form1 form2 =
	(* first find index of the rule on RHS, which can be learned on LHS *)
	let rec get_index i = 
		if (List.length form2.sigma) <= i 
		then (-1,-1)
		else 
			let res=check_learn1 ctx solv z3_names form1 form2 i in
			if res=(-1)
			then  get_index (i+1)
			else (res,i) (* res - index of z, i -index of x*)
	in
	let nequiv a b = not (a=b) in
	let remove k form =
		{ pi=form.pi;
		  sigma=List.filter (nequiv (List.nth form.sigma k)) form.sigma }
	in
	match (get_index 0) with
	| (-1,-1) -> Fail
	| (i1,i2) ->
		let y1 = 
			match (List.nth form1.sigma i1) with 
			| Hpointsto (a, _) ->  a
		in
		let y2 = 
			match (List.nth form2.sigma i2) with 
			| Hpointsto (a, _) ->  a
		in

		Apply ( { sigma=form1.sigma; pi = (BinOp ( Pneq, y1,y2))::form1.pi},
			(remove i2 form2), 
			{sigma=[List.nth form2.sigma i2]; pi=[]})


(* FINISH *)
type finish_res =
| Finish of Formula.t
| NoFinish
| FinFail

let test_finish ctx solv z3_names form1 form2 =
	if (List.length form2.sigma)>0 then NoFinish
	else
	let query = (List.append (formula_to_solver ctx form1) (formula_to_solver ctx form2)) in
	if (Solver.check solv query)=UNSATISFIABLE then FinFail
	else Finish {pi=[]; sigma=form1.sigma} (* return FRAME, pi may be not empty --- TO be Checked *)

(* main biabduction function *)

type abduction_res =
| Bok of Formula.t * Formula.t
| BFail

let rec biabduction ctx solv z3_names form1 form2 =
	match (test_finish ctx solv z3_names form1 form2) with
	| FinFail -> BFail
	| Finish frame -> Bok ( {pi=[];sigma=[]} ,frame)
	| NoFinish ->
	(* try the particular rules *)
	(* match 1 *)
	match (try_match1 ctx solv z3_names form1 form2) with
	| Apply (f1,f2,missing) -> 
		(match biabduction ctx solv z3_names f1 f2 with
		| BFail -> BFail
		| Bok (miss,fr)-> Bok ({pi=(List.append missing.pi miss.pi);sigma=(List.append missing.sigma miss.sigma)}  ,fr)
		)
	| Fail ->
	(* learn 1 *)
	match (try_learn1 ctx solv z3_names form1 form2) with
	| Apply (f1,f2,missing) -> 
		(match biabduction ctx solv z3_names f1 f2 with
		| BFail -> BFail
		| Bok (miss,fr)-> Bok ({pi=(List.append missing.pi miss.pi);sigma=(List.append missing.sigma miss.sigma)}  ,fr)
		)
	| Fail ->

		BFail

(*  Experiments
let cfg = [("model", "true"); ("proof", "false")]
let ctx = (mk_context cfg)
let solv = (Solver.mk_solver ctx None)
let z3_names=get_sl_functions_z3 ctx


check_match1 ctx solv z3_names form1 0 pre_free 0

check_learn1 ctx solv z3_names pre_free form2 1;;

try_learn1 ctx solv z3_names form1 form2;;

find_match1_ll ctx solv z3_names form1 0 pre_free

*)


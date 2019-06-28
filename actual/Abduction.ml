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

(**** MATCH rules ****)
(* The level parameter gives the level of match, the only difference is in check_match function *)

(* Check whether match (of the given level) can be applied on i1^th pointsto on LHS and i2^th points-to on RHS *)
let check_match ctx solv z3_names form1 i1 form2 i2 level =

	let lhs = 
		match (List.nth form1.sigma i1) with 
		| Hpointsto (a,_ ,_) -> (expr_to_solver ctx z3_names a) 
	in
	let lhs_size =
		match (List.nth form1.sigma i1) with 
		| Hpointsto (_, s ,_) -> s 
	in
	let rhs = 
		match (List.nth form2.sigma i2) with 
		| Hpointsto (a,_ ,_) -> (expr_to_solver ctx z3_names a) 
	in
	let rhs_size =
		match (List.nth form2.sigma i2) with 
		| Hpointsto (_, s ,_) -> s 
	in
	match level with
	| 1 ->
		let query1 = 
			[Boolean.mk_not ctx (Boolean.mk_eq ctx lhs rhs);                
				(Boolean.mk_and ctx (formula_to_solver ctx form1))
			]
		in
		let query2 = 
			[Boolean.mk_not ctx (Boolean.mk_eq ctx lhs rhs);                
				(Boolean.mk_and ctx (formula_to_solver ctx form2))
			]
		in
		(lhs_size=rhs_size) && (((Solver.check solv query1)=UNSATISFIABLE)||((Solver.check solv query2)=UNSATISFIABLE))
	| 2 -> 
		let query1=[(Boolean.mk_and ctx (formula_to_solver ctx form1));
				(Boolean.mk_and ctx (formula_to_solver ctx form1));
				(Boolean.mk_eq ctx lhs rhs)
			]
		in
		let query2=[Boolean.mk_not ctx (Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [lhs]) (Expr.mk_app ctx z3_names.base [rhs]));                
				(Boolean.mk_and ctx (formula_to_solver ctx form1))
			]
		in

		(lhs_size=rhs_size) && ((Solver.check solv query1)=SATISFIABLE) && ((Solver.check solv query2)=UNSATISFIABLE)
	| 3 -> 
		let query=[(Boolean.mk_and ctx (formula_to_solver ctx form1));
				(Boolean.mk_and ctx (formula_to_solver ctx form1));
				(Boolean.mk_eq ctx lhs rhs)
			]
		in
		(lhs_size=rhs_size) && ((Solver.check solv query)=SATISFIABLE) 
	| _ -> false

(* Find pair of points-to for match. Return (-1,-1) if unposibble *) 
let rec find_match_ll ctx solv z3_names form1 i1 form2 level=
	let rec try_with_rhs i2 =
		if (List.length form2.sigma) <= i2 
		then -1
		else (if (check_match ctx solv z3_names form1 i1 form2 i2 level) 
			then i2
			else -1)
	in
	if (List.length form1.sigma) <= i1 
	then (-1,-1)
	else
		match (try_with_rhs 0) with
		| -1 -> (find_match_ll ctx solv z3_names form1 (i1+1) form2 level)
		| x -> (i1,x) 

let find_match ctx solv z3_names form1 form2 level =
	find_match_ll ctx solv z3_names form1 0 form2 level


(* apply the match rule to i=(i1,i2)---i1^th pointsto on LHS and i2^th points-to on RHS,
   find_match must be used
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
		

(* Try to apply match rule. The result is:
	form1 - the LHS formula with removed matched part and added equality x=y
	form2 - the RHS formula with removed matched part
	M - the learned part
*)
let try_match ctx solv z3_names form1 form2 level =
	let m=find_match ctx solv z3_names form1 form2 level in
	match m with
	| (-1,-1) -> Fail
	| (i1,i2) ->
		let (f1,f2)=apply_match (i1,i2) form1 form2 in
		let x1,y1=match (List.nth form1.sigma i1) with 
			| Hpointsto (a,_,b) -> (a,b) in
		let x2,y2=match (List.nth form2.sigma i2) with 
			| Hpointsto (a,_,b) -> (a,b) in
		match level with
		| 1 -> 	Apply ( { sigma=f1.sigma; pi = (BinOp ( Peq, y1,y2))::((BinOp (Peq, x1,x2))::f1.pi)},
				f2, 
				{sigma=[]; pi=[]})
		| _ -> 	Apply ( { sigma=f1.sigma; pi = (BinOp ( Peq, y1,y2))::((BinOp (Peq, x1,x2))::f1.pi)},
				f2, 
				{sigma=[]; pi=[(BinOp (Peq, x1,x2))]})

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
		| Hpointsto (a,_ ,_) -> (expr_to_solver ctx z3_names a) (* SIZE missing *)
	in
	let lhs = 
		match (List.nth form1.sigma z) with 
		| Hpointsto (a,_, _) -> (expr_to_solver ctx z3_names a) (* SIZE missing *)
	in
	let query1= [ Boolean.mk_not ctx (
			Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [lhs]) (Expr.mk_app ctx z3_names.base [rhs])); 
			(Boolean.mk_not ctx (Boolean.mk_eq ctx lhs rhs));
			(Boolean.mk_and ctx (formula_to_solver ctx form1))
			]
	in
	let query2= [ Boolean.mk_not ctx (
			Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [lhs]) (Expr.mk_app ctx z3_names.base [rhs])); 
			(Boolean.mk_not ctx (Boolean.mk_eq ctx lhs rhs));
			(Boolean.mk_and ctx (formula_to_solver ctx form2))
			]
	in
	if ((Solver.check solv query1)=UNSATISFIABLE)||((Solver.check solv query2)=UNSATISFIABLE) then z
	else find_z ctx solv z3_names form1 (z+1) form2 i2
	
(* check whether we can apply learn on the form2.sigma[i2].
   The result is -1: imposible
   		 0...k: the index of "z" (if level=1)
		 -3: possible (if level=3)
*)
let check_learn ctx solv z3_names form1 form2 i2 level =
	let rhs = 
		match (List.nth form2.sigma i2) with 
		| Hpointsto (a,_,_) -> (expr_to_solver ctx z3_names a)
	in
	(* create list of equalities between form2.sigma[i2] and all items in form1.sigma *)
	let rec list_eq pointsto_list =
		match pointsto_list with
		| [] -> []
		| first::rest ->
			(Boolean.mk_eq ctx rhs 
				( match first with 
					| Hpointsto (a,_, _) -> (expr_to_solver ctx z3_names a))
			)
			:: list_eq rest
	in
	let query = match (list_eq form1.sigma) with
		| [] -> [ (Boolean.mk_and ctx (formula_to_solver ctx form1)); 
			  (Boolean.mk_and ctx (formula_to_solver ctx form2)) ]
		| a -> [ (Boolean.mk_not ctx (Boolean.mk_or ctx a));
			  (Boolean.mk_and ctx (formula_to_solver ctx form1)); 
			  (Boolean.mk_and ctx (formula_to_solver ctx form2)) ]
	in	
	match level with
	| 1 -> 	if ((Solver.check solv query)=SATISFIABLE) then
			find_z ctx solv z3_names form1 0 form2 i2	
		else -1
	| 3 -> if ((Solver.check solv query)=SATISFIABLE) then -3 else -1
	| _ -> -1
		

(* try to apply learn1 rule *)
let try_learn ctx solv z3_names form1 form2 level=
	(* first find index of the rule on RHS, which can be learned on LHS *)
	let rec get_index i = 
		if (List.length form2.sigma) <= i 
		then (-1,-1)
		else 
			let res=check_learn ctx solv z3_names form1 form2 i level in
			if res=(-1)
			then  get_index (i+1)
			else (res,i) (* res - index of z, i - index of x*)
	in
	let nequiv a b = not (a=b) in
	let remove k form =
		{ pi=form.pi;
		  sigma=List.filter (nequiv (List.nth form.sigma k)) form.sigma }
	in
	match (get_index 0) with
	| (-1,-1) -> Fail
	| (-3,i2) -> (* learn with level 3 *)
		Apply ( { sigma=form1.sigma; pi = form1.pi},
			(remove i2 form2), 
			{sigma=[List.nth form2.sigma i2]; pi=[]})
	| (i1,i2) -> (* learn with level 1 *)
		let y1 = 
			match (List.nth form1.sigma i1) with 
			| Hpointsto (a,_,_) ->  a
		in
		let y2 = 
			match (List.nth form2.sigma i2) with 
			| Hpointsto (a,_,_) ->  a
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
	else Finish {pi=form1.pi; sigma=form1.sigma} (* return FRAME, pi may be not empty --- TO be Checked *)

(* main biabduction function *)

type abduction_res =
| Bok of Formula.t * Formula.t
| BFail

let rec biabduction ctx solv z3_names form1 form2 =
	match (test_finish ctx solv z3_names form1 form2) with
	| FinFail -> BFail
	| Finish frame -> print_string "Finish true, "; Bok ( {pi=[];sigma=[]} ,frame)
	| NoFinish ->
	(* try the particular rules *)
	(* learn 1 *)
	match (try_learn ctx solv z3_names form1 form2 1) with
	| Apply (f1,f2,missing) -> 
		print_string "Learn1, ";
		(match biabduction ctx solv z3_names f1 f2 with
		| BFail -> BFail
		| Bok (miss,fr)-> Bok ({pi=(List.append missing.pi miss.pi);sigma=(List.append missing.sigma miss.sigma)}  ,fr)
		)
	| Fail ->
	(* match 1 *)
	match (try_match ctx solv z3_names form1 form2 1) with
	| Apply (f1,f2,missing) -> 
		print_string "Match1, ";
		(match biabduction ctx solv z3_names f1 f2 with
		| BFail -> BFail
		| Bok (miss,fr)-> Bok ({pi=(List.append missing.pi miss.pi);sigma=(List.append missing.sigma miss.sigma)}  ,fr)
		)
	| Fail ->
	(* match 2 *)
	match (try_match ctx solv z3_names form1 form2 2) with
	| Apply (f1,f2,missing) -> 
		print_string "Match2, ";
		(match biabduction ctx solv z3_names f1 f2 with
		| BFail -> BFail
		| Bok (miss,fr)-> Bok ({pi=(List.append missing.pi miss.pi);sigma=(List.append missing.sigma miss.sigma)}  ,fr)
		)
	| Fail ->
	(* match 3 *)
	match (try_match ctx solv z3_names form1 form2 3) with
	| Apply (f1,f2,missing) -> 
		print_string "Match3, ";
		(match biabduction ctx solv z3_names f1 f2 with
		| BFail -> BFail
		| Bok (miss,fr)-> Bok ({pi=(List.append missing.pi miss.pi);sigma=(List.append missing.sigma miss.sigma)}  ,fr)
		)
	| Fail ->
	(* learn 3 *)
	match (try_learn ctx solv z3_names form1 form2 3) with
	| Apply (f1,f2,missing) -> 
		print_string "Learn3, ";
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


check_match ctx solv z3_names form1 0 pre_free 0 1

check_learn1 ctx solv z3_names pre_free form2 1;;

try_learn1 ctx solv z3_names form1 form2;;

find_match_ll ctx solv z3_names form1 0 pre_free

*)


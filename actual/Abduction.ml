(* in Utop use 
	#mod_use "Formula.ml" 
   	#require "z3" 
	#mod_use "Z3wrapper.ml"
*)

open Formula
open Z3
open Z3wrapper

(** result of the rule application
    form1 * form2 * M * added_local_vars
    or Fail
**)
type res =
| Apply of Formula.t * Formula.t * Formula.t * int list
| Fail

(**** MATCH rules ****)
(* The level parameter gives the level of match, the only difference is in check_match function *)

(* Check whether match (of the given level) can be applied on i1^th pointsto on LHS and i2^th points-to on RHS *)
let check_match ctx solv z3_names form1 i1 form2 i2 level =

	let lhs = 
		match (List.nth form1.sigma i1) with 
		| Hpointsto (a,_ ,_) -> (expr_to_solver ctx z3_names a) 
		| Slseg (a,_,_) -> (expr_to_solver ctx z3_names a)
	in
	let lhs_size =
		match (List.nth form1.sigma i1) with 
		| Hpointsto (_, s ,_) -> s 
		| Slseg _ -> -1 (* we do not speak about sizes before the slseg is unfolded *)
	in
	let rhs = 
		match (List.nth form2.sigma i2) with 
		| Hpointsto (a,_ ,_) -> (expr_to_solver ctx z3_names a) 
		| Slseg (a,_,_) -> (expr_to_solver ctx z3_names a)
	in
	let rhs_size =
		match (List.nth form2.sigma i2) with 
		| Hpointsto (_, s ,_) -> s 
		| Slseg _ -> -1 (* we do not speak about sizes before the slseg is unfolded *)
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
		((lhs_size=rhs_size)||(lhs_size=(-1))||(rhs_size=(-1)))
		&& (((Solver.check solv query1)=UNSATISFIABLE)||((Solver.check solv query2)=UNSATISFIABLE))
	| 2 ->
		let query = 
			[Boolean.mk_not ctx (Boolean.mk_eq ctx lhs rhs);                
				(Boolean.mk_and ctx (formula_to_solver ctx form1));
				(Boolean.mk_and ctx (formula_to_solver ctx form2))
			]
		in
		((lhs_size=rhs_size)||(lhs_size=(-1))||(rhs_size=(-1)))
		&& ((Solver.check solv query)=UNSATISFIABLE)
	| 3 -> 
		let query1=[(Boolean.mk_and ctx (formula_to_solver ctx form1));
				(Boolean.mk_and ctx (formula_to_solver ctx form2));
				(Boolean.mk_eq ctx lhs rhs)
			]
		in
		let query2=[Boolean.mk_not ctx (Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [lhs]) (Expr.mk_app ctx z3_names.base [rhs]));                
				(Boolean.mk_and ctx (formula_to_solver ctx form1))
			]
		in

		((lhs_size=rhs_size)||(lhs_size=(-1))||(rhs_size=(-1)))
		&& ((Solver.check solv query1)=SATISFIABLE) && ((Solver.check solv query2)=UNSATISFIABLE)
	| 4 -> 
		let query=[(Boolean.mk_and ctx (formula_to_solver ctx form1));
				(Boolean.mk_and ctx (formula_to_solver ctx form2));
				(Boolean.mk_eq ctx lhs rhs)
			]
		in
		((lhs_size=rhs_size)||(lhs_size=(-1))||(rhs_size=(-1)))
		&& ((Solver.check solv query)=SATISFIABLE) 
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


(* apply the match rule to i=(i1,i2)
   pred_type=0 --- pointsto x pointsto
   pred_type=1 --- pointsto x Slseg
   pred_type=2 --- Slseg x pointsto
   pred_type=3 --- Slseg x Slseg
*)
type apply_match_res =
| ApplyOK of Formula.t * Formula.t * int list 
| ApplyFail


(* !!! Need to be tested, case 4 not finished ***)
let apply_match i pred_type form1 form2 =
	let nequiv a b = not (a=b) in
	let remove k form =
		{ pi=form.pi;
		  sigma=List.filter (nequiv (List.nth form.sigma k)) form.sigma }
	in
	match i with
	| (i1,i2) ->
		match pred_type with
		| 0 -> ApplyOK ((remove i1 form1), (remove i2 form2), [])
		| 1 -> let new_form2,new_lvars=unfold_predicate form2 i2 (find_vars form1) in
			ApplyOK (form1, new_form2, new_lvars)
		| 2 -> let new_form1,new_lvars=unfold_predicate form1 i1 (find_vars form2) in
			ApplyOK (new_form1, form2, new_lvars)
		| 3 -> 
			let y1,ls1=match (List.nth form1.sigma i1) with 
			| Slseg (_,b,f) -> b,f in
			let x2,y2,ls2=match (List.nth form2.sigma i2) with 
			| Slseg (a,b,f) -> a,b,f in
			if (ls1=ls2) then (* This is ugly hack. Should be replaced by entailment check ls1 |-ls2 *)
				let lhs=(remove i1 form1) in
				let rhs_tmp=(remove i2 form2) in
				let rhs={sigma=(Slseg (y1,y2,ls2))::rhs_tmp.sigma; pi=rhs_tmp.pi} in
				ApplyOK (lhs, rhs, [])

			else ApplyFail


(* Try to apply match rule. The result is:
1:	form1 - the LHS formula with removed matched part and added equality x=y
	form2 - the RHS formula with removed matched part
	M - the learned part
2:	unfolded Slseg in form1/form2 and added equality x=y
*)
let try_match ctx solv z3_names form1 form2 level =
	let m=find_match ctx solv z3_names form1 form2 level in
	match m with
	| (-1,-1) -> Fail
	| (i1,i2) ->
		let x1,y1,type1=match (List.nth form1.sigma i1) with 
			| Hpointsto (a,_,b) -> (a,b,0) 
			| Slseg (a,b,_) -> (a,b,2) in
		let x2,y2,type2=match (List.nth form2.sigma i2) with 
			| Hpointsto (a,_,b) -> (a,b,0)
			| Slseg (a,b,_) -> (a,b,1) in
		match apply_match (i1,i2) (type1+type2) form1 form2 with
		| ApplyFail -> Fail
		| ApplyOK (f1,f2,added_lvars) ->
			(* y1 = y2 is added only if Hpointsto is mathced with Hpointsto *)
			let y_eq=if (type1+type2)=0 then [(Exp.BinOp ( Peq, y1,y2))] else [] in
			match level with
			| 1 -> 	Apply ( { sigma=f1.sigma; pi = (BinOp (Peq, x1,x2))::(y_eq @ f1.pi)},
					f2, 
					{sigma=[]; pi=[]}, 
					added_lvars)
			| _ -> 	Apply ( { sigma=f1.sigma; pi = (BinOp (Peq, x1,x2))::(y_eq @ f1.pi)},
					f2, 
					{sigma=[]; pi=[(BinOp (Peq, x1,x2))]}, 
					added_lvars)

(**** LEARN - pointsto ****)

(* let x be: form2.sigma[i2]=x->_ 
  we know that x!= y for all y->_ \in form1.sigma
  now find a z->_ in form1.sigma such that base(z) = base(x) is valid *)
let rec find_z ctx solv z3_names form1 z form2 i2 =
	if (List.length form1.sigma) <= z
		then -1
	else
	let rhs = 
		match (List.nth form2.sigma i2) with 
		| Hpointsto (a,_ ,_) -> (expr_to_solver ctx z3_names a) (* SIZE missing *) (* RHS can be Hpointsto only *)
	in
	match (List.nth form1.sigma z) with 
		| Slseg (a,_,_) -> (find_z ctx solv z3_names form1 (z+1) form2 i2)
		| Hpointsto (a,_, _) -> 
		let lhs= (expr_to_solver ctx z3_names a) in (* SIZE missing *)
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
let check_learn_pointsto ctx solv z3_names form1 form2 i2 level =
	match (List.nth form2.sigma i2) with 
	| Slseg _ -> -1 (* Slseg is skipped, only Hpointsto is allowed in this function *)
	| Hpointsto (a,_,_) -> 
		let rhs = (expr_to_solver ctx z3_names a) in
		(* create list of equalities between form2.sigma[i2] and all items in form1.sigma *)
		let rec list_eq pointsto_list =
			match pointsto_list with
			| [] -> []
			| first::rest ->
				(match first with
				| Hpointsto (a,_, _) -> (Boolean.mk_eq ctx rhs (expr_to_solver ctx z3_names a))
				| Slseg (a,_,_) -> (Boolean.mk_eq ctx 
							(Expr.mk_app ctx z3_names.base [rhs]) 
							(Expr.mk_app ctx z3_names.base [expr_to_solver ctx z3_names a]))
				) :: list_eq rest
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
		

(* try to apply learn1 rule for pointsto *)
let try_learn_pointsto ctx solv z3_names form1 form2 level=
	(* first find index of the rule on RHS, which can be learned on LHS *)
	let rec get_index i = 
		if (List.length form2.sigma) <= i 
		then (-1,-1)
		else 
			let res=check_learn_pointsto ctx solv z3_names form1 form2 i level in
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
			{sigma=[List.nth form2.sigma i2]; pi=[]},
			[])
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
			{sigma=[List.nth form2.sigma i2]; pi=[]},
			[])

(**** LEARN - Slseg ****)

(* check whether we can apply learn on the form2.sigma[i2].
   The result is false: imposible
		 true: possible
*)

let check_learn_slseg ctx solv z3_names form1 form2 i2 level =
	match (List.nth form2.sigma i2) with 
	| Hpointsto (a,_,_) ->  false (* This funmction cover slseg learn only *)
	| Slseg (a,_,_) -> 
		let rhs = (expr_to_solver ctx z3_names a) in
		(* create diffbase(rhs) and diffls(rhs) *)
		let rec list_eq sigma =
			match sigma with
			| [] -> []
			| first::rest ->
				(match first with
				| Hpointsto (a,_, _) -> (Boolean.mk_eq ctx 
							(Expr.mk_app ctx z3_names.base [rhs]) 
							(Expr.mk_app ctx z3_names.base [expr_to_solver ctx z3_names a]))
				| Slseg (a,_,_) -> (Boolean.mk_eq ctx rhs (expr_to_solver ctx z3_names a))
				) :: list_eq rest
		in
		match level with
		| 1 -> (match  (list_eq form1.sigma) with
			| [] -> false (* learn1 can not be applied with empty sigma on LHS *)
			| a -> 
				let query = [ (Boolean.mk_and ctx (formula_to_solver ctx form1));
					 (Boolean.mk_or ctx a)]
				in 
				(Solver.check solv query)=UNSATISFIABLE
			)
		| 2 -> 	let query = 
				match (list_eq form1.sigma) with
				| [] -> [(Boolean.mk_and ctx (formula_to_solver ctx form1)); 
					(Boolean.mk_and ctx (formula_to_solver ctx form2)) ]
				| a -> 	[ (Boolean.mk_not ctx (Boolean.mk_or ctx a)); 
					(Boolean.mk_and ctx (formula_to_solver ctx form1)); 
					(Boolean.mk_and ctx (formula_to_solver ctx form2)) ] 
			in
			(Solver.check solv query)=SATISFIABLE		

(* try to apply learn rule for slseg *)
let try_learn_slseg ctx solv z3_names form1 form2 level=
	(* first find index of the rule on RHS, which can be learned on LHS *)
	let rec get_index i = 
		if (List.length form2.sigma) <= i 
		then -1
		else 
			if (check_learn_slseg ctx solv z3_names form1 form2 i level) 
			then i
			else get_index (i+1)
	in
	let nequiv a b = not (a=b) in
	let remove k form =
		{ pi=form.pi;
		  sigma=List.filter (nequiv (List.nth form.sigma k)) form.sigma }
	in
	match (get_index 0) with
	| -1 -> Fail
	| i -> Apply ( { sigma=form1.sigma; pi = form1.pi},
			(remove i form2), 
			{sigma=[List.nth form2.sigma i]; pi=[]},
			[])


(* Test SAT of (form1 /\ form2) and check finish *)
type sat_test_res =
| Finish of Formula.t
| NoFinish
| SatFail

let test_sat ctx solv z3_names form1 form2 =
	let query = (List.append (formula_to_solver ctx form1) (formula_to_solver ctx form2)) in
	if (Solver.check solv query)=UNSATISFIABLE then SatFail
	else
	if (List.length form2.sigma)>0 then NoFinish
	else Finish {pi=form1.pi; sigma=form1.sigma} (* return FRAME, pi may be not empty --- To be Checked *)

(* main biabduction function *)
(* The result is:  "missing, frame, added_lvars" *)

type abduction_res =
| Bok of Formula.t * Formula.t * int list
| BFail

let rec biabduction ctx solv z3_names form1 form2 =
	(* First test SAT of form1 and form2. 
	   Postponing SAT to the end of biabduction may lead to hidden conflicts.
	   The conflicts may be removed by application of a match rule.
	 *)
	match (test_sat ctx solv z3_names form1 form2) with
	| SatFail -> 
		print_string "SAT fail"; BFail
	| Finish frame -> print_string "Finish true, "; Bok ( {pi=[];sigma=[]} ,frame, [])
	| NoFinish ->
	(* Here is a given list of possible rules and the order in which they are going to be applied *)
	let rules=[
		(try_match,1,"Match1");
		(try_match,2,"Match2");
		(try_match,3,"Match3");
		(try_learn_pointsto,1,"Learn1-Pointsto");
		(try_learn_slseg,1,"Learn1-Slseg");
		(try_match,4,"Match4");
		(try_learn_pointsto,3,"Learn3-Pointsto");
		(try_learn_slseg,2,"Learn2-Slseg")
	] in
	(* try the rules till an applicable if founded *)
	let rec try_rules todo=
		match todo with
		| (func_name,rule_arg,rule_name) :: rest -> 
			(match (func_name ctx solv z3_names form1 form2 rule_arg) with
			| Apply (f1,f2,missing,n_lvars) -> 
				print_string (rule_name ^", ");
				Apply (f1,f2,missing,n_lvars)
			| Fail ->
				try_rules rest
			)
		| [] -> Fail
	in
	match try_rules rules with
	| Apply (f1,f2,missing,n_lvars) -> 
		(match biabduction ctx solv z3_names f1 f2 with
		| BFail -> BFail
		| Bok (miss,fr,l_vars)-> Bok ({pi=(List.append missing.pi miss.pi);sigma=(List.append missing.sigma miss.sigma)}  ,fr, n_lvars@l_vars)
		)
	| Fail -> 
		print_string "No applicable rule"; BFail
	




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


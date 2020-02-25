open Formula
open Z3
open Z3wrapper

(* TODO: 
   (1) siplify pure part inside lambda and in the main formula after folding (i.e. get rid of useless existentials)
   (2) check that you are not folding global variables 
*)


type res =
| AbstractionApply of Formula.t
| AbstractionFail

(* for a given pointer expression a1 find all spacial predicates with an equal base adress 
   include_a1=0 --- pointsto "a1 -> _" is skipped
   include_a1=1 --- pointsto "a1 -> _" is included
*) 

let rec get_eq_base ctx solv z3_names form a1 index include_a1 =
	if index=(List.length form.sigma) then []
	else
	let a2 = match (List.nth form.sigma index) with
		| Slseg (a,_,_) -> (expr_to_solver ctx z3_names a)
		| Hpointsto (a,_,_) -> (expr_to_solver ctx z3_names a)
	in
	(* form -> base(a1) = base(a2) *)
	let query=[ (Boolean.mk_and ctx (formula_to_solver ctx form));
		(Boolean.mk_not ctx (Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [a1]) (Expr.mk_app ctx z3_names.base [a2])))
	] in
	(* form -> a1 != a2 *)
	let query2= [ (Boolean.mk_and ctx (formula_to_solver ctx form));
		(Boolean.mk_not ctx (Boolean.mk_not ctx (Boolean.mk_eq ctx a1 a2)))
	] in
	match (Solver.check solv query), (Solver.check solv query2), include_a1 with
	| UNSATISFIABLE, UNSATISFIABLE, 0 -> index :: (get_eq_base ctx solv z3_names form a1 (index+1) include_a1)
	| UNSATISFIABLE, _, 1 -> index :: (get_eq_base ctx solv z3_names form a1 (index+1) include_a1)
	| _ -> (get_eq_base ctx solv z3_names form a1 (index+1) include_a1)


(* Check that points-to on i1 and i2 can have (=SAT) equal distance from base of the block *)
let check_eq_dist_from_base ctx solv z3_names form i1 i2 =
	let ff = Boolean.mk_false ctx in
	let a1,l1 = match (List.nth form.sigma i1) with
		| Slseg _ -> ff,ff
		| Hpointsto (a,l,_) -> (expr_to_solver ctx z3_names a),(expr_to_solver ctx z3_names l)
	in
	let a2,l2 = match (List.nth form.sigma i2) with
		| Slseg _ -> ff,ff
		| Hpointsto (a,l,_) -> (expr_to_solver ctx z3_names a),(expr_to_solver ctx z3_names l)
	in
	if ((a1=ff) || (a2=ff)) then false
	else
	(* SAT: form /\ a1-base(a1) = a2 - base(a2) *)
	let query1 = [ (Boolean.mk_and ctx (formula_to_solver ctx form));
		Boolean.mk_eq ctx 
			(Arithmetic.mk_sub ctx [ a1; (Expr.mk_app ctx z3_names.base [a1]) ])
			(Arithmetic.mk_sub ctx [ a2; (Expr.mk_app ctx z3_names.base [a2]) ])
	] in
	(* SAT l1=l2 *)
	let query2 = [ (Boolean.mk_and ctx (formula_to_solver ctx form));
		Boolean.mk_eq ctx l1 l2
	] in

	((Solver.check solv query1)=SATISFIABLE)&&((Solver.check solv query2)=SATISFIABLE)


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


(* Check that for variables v1 and v2 there exists a tuple (base1,base2) in block_bases s.t.
   (1) form -> base(base1) = base(v1) /\ base(base2) = base(v2)
   (2) SAT: form /\ v1-base(v1) = v2 - base(v2)
   *)
let rec check_block_bases ctx solv z3_names form v1 v2 block_bases =
	match block_bases with
	| [] -> false
	| (b1,b2)::rest ->
		let var1=expr_to_solver ctx z3_names (Exp.Var v1) in
		let var2=expr_to_solver ctx z3_names (Exp.Var v2) in
		(* form -> base(base1) = base(v1) /\ base(base2) = base(v2) *)
		let query_blocks=[ (Boolean.mk_and ctx (formula_to_solver ctx form));
			(Boolean.mk_not ctx (Boolean.mk_and ctx [
				(Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [b1]) (Expr.mk_app ctx z3_names.base [var1]));
				(Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [b2]) (Expr.mk_app ctx z3_names.base [var2]))
			]))
		] in
		(* SAT: form /\ v1-base(v1) = v2 - base(v2) *)
		let query_dist = [ (Boolean.mk_and ctx (formula_to_solver ctx form));
				Boolean.mk_eq ctx 
				(Arithmetic.mk_sub ctx [ var1; (Expr.mk_app ctx z3_names.base [var1]) ])
				(Arithmetic.mk_sub ctx [ var2; (Expr.mk_app ctx z3_names.base [var2]) ])
		] in

		if ((Solver.check solv query_blocks)=UNSATISFIABLE)&&((Solver.check solv query_dist)=SATISFIABLE) then true
		else check_block_bases ctx solv z3_names form v1 v2 rest

(* check that the pairs_of_pointsto can be folded into the list segment,
   incl_ref_blocks - include referenced blocks --- 
   	v1 -> v2 * v1+8 -> v10 * v10 -> null * v2 -> v3 *  v2+8->v11 * v11->null 
	/\ base(v1)=v1, base(v2)=v2,base(v10)=v10, base(v11)=v11)
   We call check_matched_pointsto with pairs_of_pto=[(0,3);(1,3)].
	incl_ref_blocks=1: "v10 -> null" is matched with "v11->null" and abstraction is applied
	incl_ref_blocks=0: pointsto no. 2 and 5 are not included --- abstraction fails
*)

type check_res =
| CheckOK of (int * int * heap_pred) list
| CheckFail

(* this function is quite similar to the try_pointsto_to_lseg, but is is dedicated to the blocks referenced from the blocks, which should be folded *)
let find_ref_blocks ctx solv z3_names form i1 i2 block_bases =
	let a1,l1,b1 = match (List.nth form.sigma i1) with
		| Hpointsto (a,l,b) -> (expr_to_solver ctx z3_names a),(expr_to_solver ctx z3_names l),(expr_to_solver ctx z3_names b)
	in
	let a2,l2,b2 = match (List.nth form.sigma i2) with
		| Hpointsto (a,l,b) -> (expr_to_solver ctx z3_names a),(expr_to_solver ctx z3_names l),(expr_to_solver ctx z3_names b)
	in
	(* form -> base(a1) != base(a2) /\ l1 = l2 *)
	let query1 = [	(Boolean.mk_and ctx (formula_to_solver ctx form));
		Boolean.mk_or ctx [
		(Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [a1]) (Expr.mk_app ctx z3_names.base [a2]));
		(Boolean.mk_not ctx (Boolean.mk_eq ctx l1 l2));]
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
	let a1_block=get_eq_base ctx solv z3_names form a1 0 0 in
	let a2_block=get_eq_base ctx solv z3_names form a2 0 0 in
	match match_pointsto_from_two_blocks ctx solv z3_names form a1_block a2_block with
		| MatchFail -> print_string "Recursion_failed"; false
		| MatchOK matchres -> print_string "Recursion OK"; true






let rec check_matched_pointsto ctx solv z3_names form pairs_of_pto block_bases incl_ref_blocks =
	match pairs_of_pto with
	| [] -> CheckOK []
	| (i1,i2)::rest ->
		(* Slseg can not present here *)
		print_string ("Matching pointsto no: "^ (string_of_int i1)^" and "^(string_of_int i2));
		let a1,s1,b1 = match (List.nth form.sigma i1) with
			| Hpointsto (a,s,b) -> a,s,b
		in
		let b2 = match (List.nth form.sigma i2) with
			| Hpointsto (_,_,b) -> b
		in
		print_string (" Destinations: "^(Exp.to_string b1)^", "^(Exp.to_string b2)^"\n");
		let vars_b1 = find_vars_expr b1 in
		let vars_b2 = find_vars_expr b2 in
		let eq_base var = get_eq_base ctx solv z3_names form  (expr_to_solver ctx z3_names (Exp.Var var)) 0 1 in
		let pt_refs_b1 = List.concat(List.map eq_base vars_b1) in (* <-- bug, eq_base miss b1->_, need a swithch *)
		let pt_refs_b2 = List.concat(List.map eq_base vars_b2) in
		let query=[(Boolean.mk_and ctx (formula_to_solver ctx form));
				Boolean.mk_eq ctx (expr_to_solver ctx z3_names b1) (expr_to_solver ctx z3_names b2)
			] in
		match vars_b1, vars_b2, pt_refs_b1, pt_refs_b2 with
		| _,_,[],[] -> 
			(* b1 and b2 does not points to an fixed allocated block --- i.e. only integers or undef *) 
			print_string "***V1\n";
			(match (check_matched_pointsto ctx solv z3_names form rest block_bases incl_ref_blocks),(Solver.check solv query) with
			| CheckFail,_ -> CheckFail
			| CheckOK res,SATISFIABLE -> CheckOK ((i1,i2, Hpointsto (a1,s1,b1)):: res)
			(* Here the numerical values are abstracted to "undef" ~~ any value,
			   some abstract interpretation may be added here *)
			| CheckOK res,_ ->  CheckOK ((i1,i2, Hpointsto (a1,s1,Undef)):: res)
			)
		| [x1],[x2],f1::_,f2::_ ->
			(* b1 and b2 contaisn only a single variable pointing to an allocated block *)
			print_string ("V2: "^(string_of_int f1)^":"^(string_of_int f2)^ "\n");
			match (check_block_bases ctx solv z3_names form x1 x2 block_bases), incl_ref_blocks with
			| true, _ ->
				(match (check_matched_pointsto ctx solv z3_names form rest block_bases incl_ref_blocks) with
				| CheckFail -> CheckFail
				| CheckOK res -> CheckOK ((i1,i2,(List.nth form.sigma i1)):: res)
				)
			| false, 0 -> CheckFail
			| false, 1 -> 
				if (find_ref_blocks ctx solv z3_names form f1 f2 block_bases) then print_string "XXX" else print_string "YYY";
				CheckFail (* here, we have to search the neighbouring blocks *)

		| _ ->
			(* complicated pattern -> stop abstraction *)
			print_string "fail\n"; CheckFail
			


(* fold the pointsto on indeces i1 and i2 with its neighborhood given by the list of triples of the type check_res,
  each triple consist of two indeces and a spacial predicated, which should be placed into the lambda *)
let fold_pointsto form i1 i2 res_triples =
	(* first, get only the first two elements from the triples  and store it into the tmp1, and tmp2*)
	let rec get_indeces triples =
		match triples with
		| [] -> [],[]
		| (a,b,_)::rest -> 
			match get_indeces rest with
			| a1,a2 -> (a::a1,b::a2)
	in
	let tmp1,tmp2=get_indeces res_triples in
	let neighbours= [i1;i2] @ tmp1 @ tmp2 in
	let lambda_cont= i1 :: tmp1 in
	let mem l x =
    		let eq y= (x=y) in
    		List.exists eq l
  	in
	let nomem l x = not (mem l x) in
	let rec get_new_sigma i=
		if i=(List.length form.sigma) then []
		else if (mem neighbours i) then get_new_sigma (i+1)
		else (List.nth form.sigma i) :: get_new_sigma (i+1)
	in
	let rec get_new_lambda i=
		if i=(List.length form.sigma) then []
		else if (mem lambda_cont i) then (List.nth form.sigma i) :: get_new_lambda (i+1)
		else  get_new_lambda (i+1)
	in
	(* get the parameters of the list segment *)
	let p1 = match (List.nth form.sigma i1) with
			| Hpointsto (a,_,_) -> (find_vars_expr a)
	in
	let p2,p2_lambda = match (List.nth form.sigma i2) with
			| Hpointsto (b,_,a) -> (find_vars_expr a),(find_vars_expr b)
	in
	match p1,p2,p2_lambda with (* we want only a single variable on the LHS of a pointsto *)
	| [a],[b],[b_lambda] -> 
		let lambda={param=[a;b_lambda]; 
			form=(simplify  {pi=form.pi; sigma=(get_new_lambda 0)} (List.filter (nomem [a;b_lambda]) (find_vars form)))
		} in
		AbstractionApply {pi=form.pi; sigma=(get_new_sigma 0) @ [Slseg (Exp.Var a, Exp.Var b, lambda)]}
	| _ -> AbstractionFail




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
	if ((a1=ff) || (a2=ff)) then AbstractionFail
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
	if not (((Solver.check solv query1)=UNSATISFIABLE)&& ((Solver.check solv query2)=SATISFIABLE)) then AbstractionFail
	else
	(* check all pointsto with equal bases to a1/a2 *)
	let a1_block=get_eq_base ctx solv z3_names form a1 0 0 in
	let a2_block=get_eq_base ctx solv z3_names form a2 0 0 in
	(* FIRST: try to find possible mapping between particula points-to predicates is block of a1/a2 *)
	print_string "***";
	match match_pointsto_from_two_blocks ctx solv z3_names form a1_block a2_block with
	| MatchFail -> AbstractionFail 
	| MatchOK matchres -> (* SECOND: check that the mapped pointsto behave in an equal way *)
		match (check_matched_pointsto ctx solv z3_names form matchres [(a1,a2)] 1) with
		| CheckOK checked_matchres -> (fold_pointsto form i1 i2 checked_matchres)
		| CheckFail -> AbstractionFail

(***** Experiments *****)
let form_abstr1 = {
    sigma = [ Hpointsto (Var 1,ptr_size, Var 2); Hpointsto(BinOp ( Pplus, Var 1, ptr_size),ptr_size, Var 10);
    	Hpointsto (Var 2,ptr_size, Var 3); Hpointsto (BinOp ( Pplus, Var 2, ptr_size),ptr_size, Var 10)];
    pi = [ BinOp ( Peq, Var 1, UnOp ( Base, Var 1));
        BinOp ( Peq, Var 2, UnOp ( Base, Var 2))
        ]
}

let form_abstr2 = {
    sigma = [ Hpointsto (Var 1,ptr_size, Var 2); Hpointsto(BinOp ( Pplus, Var 1, ptr_size),ptr_size, Var 10);
    	Hpointsto (Var 2,ptr_size, Var 3); Hpointsto (BinOp ( Pplus, Var 2, ptr_size),ptr_size, Var 10)];
    pi = [ BinOp ( Peq, Var 1, UnOp ( Base, BinOp ( Pplus, Var 1, ptr_size)));
    	BinOp ( Peq, Var 1, UnOp ( Base, Var 1));
        BinOp ( Peq, Var 2, UnOp ( Base, Var 2));
	BinOp ( Peq, Var 2, UnOp ( Base, BinOp ( Pplus, Var 2, ptr_size)))
        ]
}

let form_abstr3 = {
    sigma = [ Hpointsto (Var 1,ptr_size, Var 2); Hpointsto(BinOp ( Pplus, Var 1, ptr_size),ptr_size, Var 10);
    	Hpointsto (Var 2,ptr_size, Var 3); Hpointsto (BinOp ( Pplus, Var 2, ptr_size),ptr_size, Var 10)];
    pi = [
    	BinOp ( Peq, Var 1, UnOp ( Base, Var 1));
    	BinOp ( Peq, UnOp ( Len, Var 1), Const (Int 16));
        BinOp ( Peq, Var 2, UnOp ( Base, Var 2));
    	BinOp ( Peq, UnOp ( Len, Var 2), Const (Int 16));
        ]
}

let form_abstr4 = {
    sigma = [ Hpointsto (Var 1,ptr_size, Var 2); Hpointsto(BinOp ( Pplus, Var 1, ptr_size),ptr_size, Var 10);
    	Hpointsto (Var 2,ptr_size, Var 3); Hpointsto (BinOp ( Pplus, Var 2, ptr_size),ptr_size, Var 10);
    	Hpointsto (Var 3,ptr_size, Var 4); Hpointsto (BinOp ( Pplus, Var 3, ptr_size),ptr_size, Var 10)];
    pi = [
    	BinOp ( Peq, Var 1, UnOp ( Base, Var 1));
    	BinOp ( Peq, UnOp ( Len, Var 1), Const (Int 16));
        BinOp ( Peq, Var 2, UnOp ( Base, Var 2));
    	BinOp ( Peq, UnOp ( Len, Var 2), Const (Int 16));
        BinOp ( Peq, Var 3, UnOp ( Base, Var 3));
    	BinOp ( Peq, UnOp ( Len, Var 3), Const (Int 16));
        ]
}
let form_abstr5 = {
    sigma = [ Hpointsto (Var 1,ptr_size, Var 2); Hpointsto(BinOp ( Pplus, Var 1, ptr_size),ptr_size, Var 10);
    	Hpointsto(BinOp ( Pplus, Var 1, Exp.Const (Int 16)),ptr_size, Var 1);
    	Hpointsto (Var 2,ptr_size, Var 3); Hpointsto (BinOp ( Pplus, Var 2, ptr_size),ptr_size, Var 10);
    	Hpointsto(BinOp ( Pplus, Var 2, Exp.Const (Int 16)),ptr_size, Var 2)];
    pi = [
    	BinOp ( Peq, Var 1, UnOp ( Base, Var 1));
    	BinOp ( Peq, UnOp ( Len, Var 1), Const (Int 32));
        BinOp ( Peq, Var 2, UnOp ( Base, Var 2));
    	BinOp ( Peq, UnOp ( Len, Var 2), Const (Int 32));
        ]
}

let form_abstr6 = {
    sigma = [ Hpointsto (Var 1,ptr_size, Var 2); Hpointsto(BinOp ( Pplus, Var 1, ptr_size),ptr_size, Var 10);
    	Hpointsto (Var 10,ptr_size, Var 1); 
    	Hpointsto (Var 2,ptr_size, Var 3); Hpointsto (BinOp ( Pplus, Var 2, ptr_size),ptr_size, Var 11);
    	Hpointsto (Var 11,ptr_size, Var 2)
	];
    pi = [
    	BinOp ( Peq, Var 1, UnOp ( Base, Var 1));
    	BinOp ( Peq, UnOp ( Len, Var 1), Const (Int 16));
    	BinOp ( Peq, Var 10, UnOp ( Base, Var 10));
        BinOp ( Peq, Var 2, UnOp ( Base, Var 2));
    	BinOp ( Peq, UnOp ( Len, Var 2), Const (Int 16));
    	BinOp ( Peq, Var 11, UnOp ( Base, Var 11));
        ]
}

(*
let x=match (try_pointsto_to_lseg ctx solv z3_names form_abstr2 0 2) with
| AbstractionApply x -> x;;

print_formula x;;
check_all_lambdas ctx solv x.sigma ;;

*)

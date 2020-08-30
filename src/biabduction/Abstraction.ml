open Formula
open Z3
open Z3wrapper

(* TODO: 
   (1) siplify pure part inside lambda and in the main formula after folding (i.e. get rid of useless existentials)
   (2) check that you are not folding global variables 
*)

exception ErrorInAbstraction of string

type res =
| AbstractionApply of Formula.t
| AbstractionFail

(* for a given pointer expression a1 find all spacial predicates with an equal base adress 
   include_a1=0 --- pointsto "a1 -> _" is skipped
   include_a1=1 --- pointsto "a1 -> _" is included
   skip --- a list of poinsto which are skipped within the test
*) 

let rec get_eq_base ctx solv z3_names form a1 index include_a1 skip =
	if index=(List.length form.sigma) then []
	else
	let mem l x =
    		let eq y= (x=y) in
    		List.exists eq l
  	in
	if (mem skip index) 
	then  (get_eq_base ctx solv z3_names form  a1 (index+1) include_a1 skip)
	else
	let a2 = match (List.nth form.sigma index) with
		| Hpointsto (a,_,_) -> (expr_to_solver ctx z3_names a)
		| Slseg (a,_,_) -> (expr_to_solver ctx z3_names a)
	in
	(* form -> base(a1) = base(a2) *)
	let query=[ (Boolean.mk_and ctx (formula_to_solver ctx form));
		(Boolean.mk_not ctx (Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [a1]) (Expr.mk_app ctx z3_names.base [a2])))
	] in
	(* form -> a1 != a2 *)
	let query2= [  (Boolean.mk_and ctx (formula_to_solver ctx form));
		(Boolean.mk_not ctx (Boolean.mk_not ctx (Boolean.mk_eq ctx a1 a2)))
	] in
	match (Solver.check solv query), (Solver.check solv query2), include_a1 with
	| UNSATISFIABLE, UNSATISFIABLE, 0 -> index :: (get_eq_base ctx solv z3_names form  a1 (index+1) include_a1 skip)
	| UNSATISFIABLE, _, 1 -> index :: (get_eq_base ctx solv z3_names form  a1 (index+1) include_a1 skip)
	| _ -> (get_eq_base ctx solv z3_names form  a1 (index+1) include_a1 skip)


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
			(BitVector.mk_sub ctx  a1 (Expr.mk_app ctx z3_names.base [a1]) )
			(BitVector.mk_sub ctx  a2 (Expr.mk_app ctx z3_names.base [a2]) )
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
				(BitVector.mk_sub ctx  var1 (Expr.mk_app ctx z3_names.base [var1]) )
				(BitVector.mk_sub ctx  var2 (Expr.mk_app ctx z3_names.base [var2]) )
		] in

		if ((Solver.check solv query_blocks)=UNSATISFIABLE)&&((Solver.check solv query_dist)=SATISFIABLE) then true
		else check_block_bases ctx solv z3_names form v1 v2 rest

(* use entailment form the Abduction module to check entailment between lambdas 
  results: 0: no entailment, 1: lambda1 |= lambda2, 2: lambda2 |= lambda1 
*)
let check_lambda_entailment ctx solv z3_names lambda1 lambda2 =
	if not ((List.length lambda1.param) = (List.length lambda2.param)) then 0
	else
	let variables= (find_vars lambda1.form) @ (find_vars lambda2.form) in
	let rec fresh_var_id intlist id=
		match intlist with 
		| [] -> id
		| first::rest -> if (first>=id) then fresh_var_id rest (first+1) else fresh_var_id rest id 
	in
	let rec get_unique_lambda_params params id =
		match params with
		| [] -> []
		| _::rest -> id::(get_unique_lambda_params rest (id+1))
	in
	let new_params=get_unique_lambda_params lambda1.param (fresh_var_id variables 0) in
	let rec rename_params form oldparams newparams =
		match oldparams,newparams with
		| [],[] -> form
		| p1::rest1,p2::rest2 -> rename_params (substitute_vars p2 p1 form) rest1 rest2
		| _ -> raise (ErrorInAbstraction "This should not happen") (*{sigma=[];pi=[]}*)
	in
	let lambda1_new= rename_params lambda1.form lambda1.param new_params in
	let lambda2_new= rename_params lambda2.form lambda2.param new_params in
	match (Abduction.entailment ctx solv z3_names lambda1_new lambda2_new variables), 
		(Abduction.entailment ctx solv z3_names lambda2_new lambda1_new variables)
	with
	| true,_ -> 1
	| false,true -> 2
	| _ -> 0



(*************************************************************************************************************)
(* Main part of the "BLOCK * BLOCK -> SLSEG" abstraction = functions:
   * check_matched_pointsto 
   	- get a paired number of pointsto from two blocks = these two blocks are candidates for abstraction intos Slseg
	- the function check possibility of folding and prepare the resulting spacial part of lambda (see heap_pred in check_res)
	- if there is a pointer reference to another blocks, the function find_ref_blocks is called (only if incl_ref_blocks=1)
   * find_ref_blocks
        - check that the predicates i1 and i2 are in different memory blocks
	- call recursivelly check_matched_pointsto with incl_ref_blocks=0
*)


type check_res =
| CheckOK of (int * int * heap_pred) list
| CheckFail

(* this function is quite similar to the try_pointsto_to_lseg, but is is dedicated to the blocks referenced from the blocks, which should be folded *)
let rec find_ref_blocks ctx solv z3_names form i1 i2 block_bases gvars=
	let global_bases base g=Boolean.mk_not ctx
		(Boolean.mk_eq ctx
			(Expr.mk_app ctx z3_names.base [base]) 
			(Expr.mk_app ctx z3_names.base [(expr_to_solver ctx z3_names (Exp.Var g))])
		)
	in
	match (List.nth form.sigma i1), (List.nth form.sigma i2) with
	| Hpointsto (a,l,_), Hpointsto (aa,ll,_) ->
		let a1,l1 = (expr_to_solver ctx z3_names a),(expr_to_solver ctx z3_names l) in
		let a2,l2 = (expr_to_solver ctx z3_names aa),(expr_to_solver ctx z3_names ll) in
		(* form -> base(a1) != base(a2) /\ l1 = l2 *)
		let query1 = [	(Boolean.mk_and ctx (formula_to_solver ctx form));
			Boolean.mk_or ctx [
			(Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [a1]) (Expr.mk_app ctx z3_names.base [a2]));
			(Boolean.mk_not ctx (Boolean.mk_eq ctx l1 l2));]
		] in
		(* SAT: form /\ a1-base(a1) = a2 - base(a2) *)
		let query2 = [ (Boolean.mk_and ctx (formula_to_solver ctx form));
			Boolean.mk_eq ctx 
			(BitVector.mk_sub ctx  a1 (Expr.mk_app ctx z3_names.base [a1]) )
			(BitVector.mk_sub ctx  a2 (Expr.mk_app ctx z3_names.base [a2]) )
		] in
		(* SAT: forall g in gvar. base(g)!=base(a1) /\ base(g)!=base(a2) *)
		let query3=if gvars=[] then []
			else
			[ (Boolean.mk_and ctx (formula_to_solver ctx form));
				Boolean.mk_and ctx (List.map (global_bases a1) gvars);
				Boolean.mk_and ctx (List.map (global_bases a2) gvars);] 
		in
		if not (((Solver.check solv query1)=UNSATISFIABLE)
			&& ((Solver.check solv query2)=SATISFIABLE)
			&& ((Solver.check solv query3)=SATISFIABLE)) then CheckFail
		else
		(* check all pointsto with equal bases to a1/a2 *)
		let a1_block=get_eq_base ctx solv z3_names form a1 0 1 [i2] in
		let a2_block=get_eq_base ctx solv z3_names form a2 0 1 (i1::a1_block) in
		(match match_pointsto_from_two_blocks ctx solv z3_names form a1_block a2_block with
			| MatchFail -> CheckFail
			| MatchOK matchres ->  
				(match (check_matched_pointsto ctx solv z3_names form matchres ((a1,a2)::block_bases) 0 gvars) with
					| CheckOK checked_matchres -> CheckOK  checked_matchres
					| CheckFail -> CheckFail
				)
		)
	| Slseg(a1,b1,l1), Slseg(a2,b2,l2) -> ( 
		let vars_b1 = find_vars_expr b1 in
		let vars_b2 = find_vars_expr b2 in
		let eq_base var = get_eq_base ctx solv z3_names form  (expr_to_solver ctx z3_names (Exp.Var var)) 0 1 [] in
		let pt_refs_b1 = List.concat(List.map eq_base vars_b1) in 
		let pt_refs_b2 = List.concat(List.map eq_base vars_b2) in
		let query=[(Boolean.mk_and ctx (formula_to_solver ctx form));
				Boolean.mk_eq ctx (expr_to_solver ctx z3_names b1) (expr_to_solver ctx z3_names b2)
			] in
		(* check entailment between l1 and l2 *)
		let entailment_res=check_lambda_entailment ctx solv z3_names l1 l2 in
		if entailment_res=0 then CheckFail
		else
		let new_lambda=if (entailment_res=1) then l2 else l1 in
		(* check that a1 and a2 are not is equal base with a global variable *)
		(* SAT: forall g in gvar. base(g)!=base(a1) /\ base(g)!=base(a2) *)
		let query3=if gvars=[] then []
			else
			[ (Boolean.mk_and ctx (formula_to_solver ctx form));
				Boolean.mk_and ctx (List.map (global_bases (expr_to_solver ctx z3_names a1)) gvars);
				Boolean.mk_and ctx (List.map (global_bases (expr_to_solver ctx z3_names a2)) gvars);] 
		in
		if ((Solver.check solv query3)=UNSATISFIABLE) then CheckFail
		else
		(* check compatibility of b1 and b2 *)
		match vars_b1, vars_b2, pt_refs_b1, pt_refs_b2 with
		| _,_,[],[] -> (* there is no referenced predicate in sigma by b1 and b2  -> check sat *)
			if (Solver.check solv query)=SATISFIABLE then CheckOK [(i1,i2,Slseg(a1,b1,new_lambda))]
			else CheckOK [(i1,i2,Slseg(a1,Undef,new_lambda))]
		| [x1],[x2],_::_,_::_ -> (* b1 and b2 refers to a predicate in sigma *) 
			if (check_block_bases ctx solv z3_names form x1 x2 
				((expr_to_solver ctx z3_names a1,expr_to_solver ctx z3_names a2 )::block_bases)) 
			then CheckOK [(i1,i2,Slseg(a1,b1,new_lambda))]
			else CheckFail
		
		| _ -> CheckFail
		)
	| _ -> CheckFail (* Slseg can not be matched with Hpointsto *)


and check_matched_pointsto ctx solv z3_names form pairs_of_pto block_bases incl_ref_blocks gvars=
	match pairs_of_pto with
	| [] -> CheckOK []
	| (i1,i2)::rest ->
		(* Slseg can not present here *)
		let a1,s1,b1 = match (List.nth form.sigma i1) with
			| Hpointsto (a,s,b) -> a,s,b
			| Slseg _ -> Exp.Void,Exp.Void,Exp.Void (* this case should not happen *)
		in
		let a2,b2 = match (List.nth form.sigma i2) with
			| Hpointsto (a,_,b) -> a,b
			| Slseg _ -> Exp.Void,Exp.Void (* this case should not happen *)
		in
		let vars_b1 = find_vars_expr b1 in
		let vars_b2 = find_vars_expr b2 in
		let eq_base var = get_eq_base ctx solv z3_names form  (expr_to_solver ctx z3_names (Exp.Var var)) 0 1 [] in
		let pt_refs_b1 = List.concat(List.map eq_base vars_b1) in 
		let pt_refs_b2 = List.concat(List.map eq_base vars_b2) in
		let query=[(Boolean.mk_and ctx (formula_to_solver ctx form));
				Boolean.mk_eq ctx (expr_to_solver ctx z3_names b1) (expr_to_solver ctx z3_names b2)
			] in
		match vars_b1, vars_b2, pt_refs_b1, pt_refs_b2 with
		| _,_,[],[] -> 
			(* b1 and b2 does not points to an fixed allocated block --- i.e. only integers or undef *) 
			(match (check_matched_pointsto ctx solv z3_names form rest block_bases incl_ref_blocks gvars),(Solver.check solv query) with
			| CheckFail,_ -> CheckFail
			| CheckOK res,SATISFIABLE -> CheckOK ((i1,i2, Hpointsto (a1,s1,b1)):: res)
			(* Here the numerical values are abstracted to "undef" ~~ any value,
			   some abstract interpretation may be added here *)
			| CheckOK res,_ ->  CheckOK ((i1,i2, Hpointsto (a1,s1,Undef)):: res)
			)
		| [x1],[x2],f1::_,f2::_ ->
			(* b1 and b2 contaisn only a single variable pointing to an allocated block *)
			(match (check_block_bases ctx solv z3_names form x1 x2 block_bases), incl_ref_blocks with
			| true, _ ->
				(match (check_matched_pointsto ctx solv z3_names form rest block_bases incl_ref_blocks gvars) with
				| CheckFail -> CheckFail
				| CheckOK res -> CheckOK ((i1,i2,(List.nth form.sigma i1)):: res)
				)
			| false, 0 -> CheckFail
			| false, _ -> 
				(match (find_ref_blocks ctx solv z3_names form f1 f2 block_bases gvars) with
				| CheckFail -> CheckFail
				| CheckOK res_rec ->
					(match (check_matched_pointsto ctx solv z3_names form rest 
						((expr_to_solver ctx z3_names a1,expr_to_solver ctx z3_names a2 )::block_bases) incl_ref_blocks gvars) with
					| CheckFail -> CheckFail
					| CheckOK res -> CheckOK ((i1,i2,(List.nth form.sigma i1)):: (res @ res_rec))
					)
				)
			)


		| _ ->
			(* complicated pattern -> stop abstraction *)
			prerr_endline "fail"; CheckFail
			


(* fold the pointsto into a existing list segment using the unfolded version of the slseg *)
let fold_pointsto_slseg form i2_orig unfolded_form new_i1 new_i2 res_triples flag =
	let rec range i j = if i > j then [] else i :: (range (i+1) j) in
	let i_unfolded_slseg=(List.length unfolded_form.sigma)-1 in (* index of the partially unfolded slseg *)
	let rec get_indeces triples =
		match triples with
		| [] -> [],[]
		| (a,b,_)::rest -> 
			match get_indeces rest with
			| a1,a2 -> (a::a1,b::a2)
	in
	let tmp1,tmp2=get_indeces res_triples in
	(* new_i2 :: tmp2 must contain all inceces from (List.length form.sigma)-1 to (List.length unfolded_form.sigma)-2 *)
	if not (List.sort compare (new_i2 :: tmp2) = range ((List.length form.sigma)-1) (i_unfolded_slseg-1))
	then raise (ErrorInAbstraction "BAD indeces")  (* AbstractionFail *)
	else
	let mem l x =
    		let eq y= (x=y) in
    		List.exists eq l
  	in
	let nomem l x = not (mem l x) in
	(* indeces to be removed from unfolded_form *)
	let to_remove=[new_i1;new_i2]@tmp1@tmp2@[i_unfolded_slseg] in
	let rec get_new_sigma i=
		if i=(List.length unfolded_form.sigma) then []
		else if (mem to_remove i) then get_new_sigma (i+1)
		else (List.nth unfolded_form.sigma i) :: get_new_sigma (i+1)
	in
	(* lambda may be overaproximated during the matches *)
	let rec new_lambda_from_triples triples =
		match triples with 
		| [] -> []
		| (_,_,l)::rest -> l :: new_lambda_from_triples rest
	in
	let rec get_fresh_var s confl=
 	   if (mem confl s)
	    then get_fresh_var (s+1) confl
	    else s
	in
	let get_new_lambda=match (List.nth unfolded_form.sigma new_i1) with
		| Hpointsto (a,l,b) ->(
			match (find_vars_expr b) with
			| _::[] -> Hpointsto (a,l,b) ::new_lambda_from_triples res_triples
			| _ -> Hpointsto (a,l,Exp.Var (get_fresh_var 0 (find_vars unfolded_form))) 
				::new_lambda_from_triples res_triples (* change null/undef or equations for fresch variable *)
			)
		| _ -> raise (ErrorInAbstraction "Something bad happened, probably broken unfolding") (*[]*)
	in
	(* get the parameters of the list segment *)
	let pto_a,pto_b = match (List.nth unfolded_form.sigma new_i1) with
			| Hpointsto (a,_,b) -> (find_vars_expr a),(find_vars_expr b)
			| Slseg _ -> [],[]
	in
	let slseg_b,lambda = match (List.nth unfolded_form.sigma i_unfolded_slseg) with
			| Hpointsto _ -> [],{param=[]; form=empty}
			| Slseg (_,b,lambda) -> (find_vars_expr b),lambda
	in
	let slseg_a_orig,slseg_b_orig,lambda_orig = match (List.nth form.sigma i2_orig) with
			| Hpointsto _ -> [],[],{param=[]; form=empty}
			| Slseg (a,b,lambda) -> (find_vars_expr a),(find_vars_expr b),lambda
	in
	(* this is a safety check that unfolding works correctly. In theory, it is not needed *)
	if not ((slseg_b=slseg_b_orig) && (lambda=lambda_orig) ) then raise (ErrorInAbstraction "Abstraction: Something bad with unfolding") (*AbstractionFail*)
	else
	let p1,p2,p1_lambda,p2_lambda=
		if flag=0 then pto_a,slseg_b,pto_a,slseg_a_orig 
		else slseg_a_orig,pto_b,pto_a,pto_b
	in
	match p1,p2,p1_lambda,p2_lambda with
	| [a],[b],[a_lambda],[b_lambda] ->
		let lambda={param=[a_lambda;b_lambda]; 
			form=(simplify  {pi=unfolded_form.pi; sigma=get_new_lambda} (List.filter (nomem [a_lambda;b_lambda]) (find_vars unfolded_form)))
		} in
		AbstractionApply {pi=unfolded_form.pi; sigma=(get_new_sigma 0) @ [Slseg (Exp.Var a, Exp.Var b, lambda)]}
	| _ -> AbstractionFail



(* check that the pointsto (and its neighbourhood) is compatible with lambda in the slseg 
  it works as follows: 
  1) the slseg is unfolded
  2) the match_pointsto_from_two_blocks and check_matched_pointsto ctx solv are used to check whether the pointsto is compatible with lambda 
  3) lambda may be updated

  flag: 0: pointsto(x,y) * slseg(y,z)
        1: slseg(x,y) * pointsto(y,z)
*)
let try_add_slseg_to_pointsto ctx solv z3_names form i_pto i_slseg gvars flag=
	let unfolded_form,_=unfold_predicate form i_slseg gvars in
	let i_unfolded_slseg=(List.length unfolded_form.sigma)-1 in (* index of the partially unfolded slseg *)
	let new_i1=if i_pto<i_slseg then i_pto else (i_pto-1) in
	(* serch for the index i2 in the unfolded_form,
	   i2 is within the unfolded part of the formula, which 
	   starts at index="(List.length form.sigma)-1"*)
	let rec find_new_i2 a1 l1 b1 index =
		if index=(List.length unfolded_form.sigma) then -1
		else
		match (List.nth unfolded_form.sigma index) with
		| Hpointsto (aa,ll,bb) ->
			let a2,l2,_= (expr_to_solver ctx z3_names aa),(expr_to_solver ctx z3_names ll),(expr_to_solver ctx z3_names bb)  in
			(* First do a base check --- i.e. query1 + query2 *)
			(* flag=0: form -> base(a1) != base(a2) /\ l1 = l2 /\ base(b1) = base(a2) *)
			(* flag=1: form -> base(a1) != base(a2) /\ l1 = l2 /\ base(endlist) = base(a1) *)
			let endlist = (* get the expression at the end of the unfolded list *)
				match (List.nth unfolded_form.sigma  i_unfolded_slseg) with
				| Slseg (_,b,_) -> (expr_to_solver ctx z3_names b)
				| _ -> raise (ErrorInAbstraction "Incompatible unfolding")
			in
			let e1,e2=if flag=0 then b1,a2 else endlist,a1 in
			let query1 = [	(Boolean.mk_and ctx (formula_to_solver ctx unfolded_form));
				Boolean.mk_or ctx [
					(Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [a1]) (Expr.mk_app ctx z3_names.base [a2]));
					(Boolean.mk_not ctx (Boolean.mk_eq ctx l1 l2));
					(Boolean.mk_not ctx (Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [e1]) (Expr.mk_app ctx z3_names.base [e2])))]
			] in
			(* SAT: form /\ a1-base(a1) = a2 - base(a2) *)
			let query2 = [ (Boolean.mk_and ctx (formula_to_solver ctx unfolded_form));
				Boolean.mk_eq ctx 
					(BitVector.mk_sub ctx  a1 (Expr.mk_app ctx z3_names.base [a1]) )
					(BitVector.mk_sub ctx  a2 (Expr.mk_app ctx z3_names.base [a2]) )
			] in
			if not (((Solver.check solv query1)=UNSATISFIABLE)
			&& ((Solver.check solv query2)=SATISFIABLE)) then (find_new_i2 a1 l1 b1 (index+1))
			else  index

		| _ -> find_new_i2 a1 l1 b1 (index+1)
	in
	(* sanity check that the unfolding works ok *)
	if not ((List.nth form.sigma i_pto)=(List.nth unfolded_form.sigma new_i1)) 
	then raise (ErrorInAbstraction "This should not happen - Problem with unfolding") (*AbstractionFail*)
	else
	match (List.nth unfolded_form.sigma new_i1) with
	| Hpointsto (a,l,b) -> (
		let a1,l1,b1= (expr_to_solver ctx z3_names a), (expr_to_solver ctx z3_names l),(expr_to_solver ctx z3_names b) in
		let new_i2=find_new_i2 a1 l1 b1 ((List.length form.sigma)-1) in (* try to find i2 in the unfolded part of the formula *)
		if (new_i2=(-1)) then AbstractionFail
		else
		let a2= match (List.nth unfolded_form.sigma new_i2) with
			| Hpointsto (aa,_,_) -> (expr_to_solver ctx z3_names aa) 
			| _ -> raise (ErrorInAbstraction "This should not happen")
		in
		let a1_block=get_eq_base ctx solv z3_names unfolded_form a1 0 0 [new_i1;new_i2] in
		let a2_block=get_eq_base ctx solv z3_names unfolded_form a2 0 0 ([new_i1;new_i2]@a1_block) in
		(* FIRST: try to find possible mapping between particular points-to predicates is block of a1/a2 *)
		match match_pointsto_from_two_blocks ctx solv z3_names unfolded_form a1_block a2_block with
		| MatchFail -> AbstractionFail 
		| MatchOK matchres ->  
			match (check_matched_pointsto ctx solv z3_names unfolded_form matchres [(a1,a2)] 1 gvars) with
			| CheckOK checked_matchres -> 
				fold_pointsto_slseg form i_slseg unfolded_form new_i1 new_i2 checked_matchres flag

			| CheckFail -> AbstractionFail
	)
	| _ -> AbstractionFail
	

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
	(* lambda may be overaproximated during the matches *)
	let rec new_lambda_from_triples triples =
		match triples with 
		| [] -> []
		| (_,_,l)::rest -> l :: new_lambda_from_triples rest
	in
	let get_new_lambda=
		(List.nth form.sigma i1):: new_lambda_from_triples res_triples
	in
	(* get the parameters of the list segment *)
	let p1 = match (List.nth form.sigma i1) with
			| Hpointsto (a,_,_) -> (find_vars_expr a)
			| Slseg _ -> []
	in
	let p2,p2_lambda = match (List.nth form.sigma i2) with
			| Hpointsto (b,_,a) -> (find_vars_expr a),(find_vars_expr b)
			| Slseg _ -> [],[]
	in
	match p1,p2,p2_lambda with (* we want only a single variable on the LHS of a pointsto *)
	| [a],[b],[b_lambda] -> 
		let lambda={param=[a;b_lambda]; 
			form=(simplify  {pi=form.pi; sigma=(get_new_lambda)} (List.filter (nomem [a;b_lambda]) (find_vars form)))
		} in
		AbstractionApply {pi=form.pi; sigma=(get_new_sigma 0) @ [Slseg (Exp.Var a, Exp.Var b, lambda)]}
	| _ -> AbstractionFail



let try_abstraction_to_lseg ctx solv z3_names form i1 i2 pvars =
(* try to abstract two predicates i1 and i2 into a list segment,
  pvars = program variables (global vars + vars of function).
      Internal nodes of the list segment can not be pointed by global variables*)
  	(* SAT: forall g in gvar. base(g)!=base(middle) *)
	let global_bases middle g=Boolean.mk_not ctx
			(Boolean.mk_eq ctx
				(Expr.mk_app ctx z3_names.base [middle]) 
				(Expr.mk_app ctx z3_names.base [(expr_to_solver ctx z3_names (Exp.Var g))])
			)
	in
	let query_pvars middle=if pvars=[] then []
		else
		[ (Boolean.mk_and ctx (formula_to_solver ctx form));
			Boolean.mk_and ctx (List.map (global_bases middle) pvars) ] 
	in
	match (List.nth form.sigma i1), (List.nth form.sigma i2) with
	| Hpointsto (a,l,b), Hpointsto (aa,ll,bb) -> (
		let a1,l1,b1= (expr_to_solver ctx z3_names a),(expr_to_solver ctx z3_names l),(expr_to_solver ctx z3_names b) in
		let a2,l2,_= (expr_to_solver ctx z3_names aa),(expr_to_solver ctx z3_names ll),(expr_to_solver ctx z3_names bb) in
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
				(BitVector.mk_sub ctx a1 (Expr.mk_app ctx z3_names.base [a1]) )
				(BitVector.mk_sub ctx a2 (Expr.mk_app ctx z3_names.base [a2]) )
		] in
		if not (((Solver.check solv query1)=UNSATISFIABLE)
			&& ((Solver.check solv query2)=SATISFIABLE)
			&& ((Solver.check solv (query_pvars a2))=SATISFIABLE)) then AbstractionFail
		else
		(* check all pointsto with equal bases to a1/a2 *)
		let a1_block=get_eq_base ctx solv z3_names form a1 0 0 [i1;i2] in
		let a2_block=get_eq_base ctx solv z3_names form a2 0 0 ([i1;i2]@a1_block) in
		(* FIRST: try to find possible mapping between particula points-to predicates is block of a1/a2 *)
		match match_pointsto_from_two_blocks ctx solv z3_names form a1_block a2_block with
		| MatchFail -> AbstractionFail 
		| MatchOK matchres -> (* SECOND: check that the mapped pointsto behave in an equal way *)
			match (check_matched_pointsto ctx solv z3_names form matchres [(a1,a2)] 1 pvars) with
			| CheckOK checked_matchres -> (fold_pointsto form i1 i2 checked_matchres)
			| CheckFail -> AbstractionFail
		)
	| Slseg(a,b,l1), Slseg(aa,bb,l2) -> (
		let b1= (expr_to_solver ctx z3_names b) in
		let a2= (expr_to_solver ctx z3_names aa) in
		(* form -> b1 = a2 *)
		let query1 = [	(Boolean.mk_and ctx (formula_to_solver ctx form));
				(Boolean.mk_not ctx (Boolean.mk_eq ctx b1 a2))
		] in
		if (Solver.check solv query1)=SATISFIABLE 
			|| ((Solver.check solv (query_pvars a2))=UNSATISFIABLE) then AbstractionFail
		else
		let rec remove_i1_i2 ll index=
			if index=List.length ll then []
			else if (index=i1) || (index=i2) then remove_i1_i2 ll (index+1)
			else (List.nth ll index) :: remove_i1_i2 ll (index+1) 
		in
			
		(match (check_lambda_entailment ctx solv z3_names l1 l2) with
			| 1 -> AbstractionApply {pi=form.pi; sigma=Slseg(a,bb,l2) :: (remove_i1_i2 form.sigma 0)}
			| 2 -> AbstractionApply {pi=form.pi; sigma=Slseg(a,bb,l1) :: (remove_i1_i2 form.sigma 0)}
			| _ -> AbstractionFail
		)
	)
	| Hpointsto (_,_,b), Slseg (aa,_,_) -> (
		let b1= (expr_to_solver ctx z3_names b) in
		let a2= (expr_to_solver ctx z3_names aa) in
		(* form -> base(b1) = base(a2) *)
		let query1 = [	(Boolean.mk_and ctx (formula_to_solver ctx form));
				(Boolean.mk_not ctx (Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [b1]) (Expr.mk_app ctx z3_names.base [a2])))
		] in		
		if (Solver.check solv query1)=SATISFIABLE 
			|| ((Solver.check solv (query_pvars a2))=UNSATISFIABLE) then AbstractionFail
		else
		(* the process continues as follows: Slseg on is unfolded and then similar process as folding of Hpointsto x Hpointsto is appplied *)
		try_add_slseg_to_pointsto ctx solv z3_names form i1 i2 pvars 0

	)
	|  Slseg (_,b,_),Hpointsto (aa,_,_) -> (
		let b1= (expr_to_solver ctx z3_names b) in
		let a2= (expr_to_solver ctx z3_names aa) in
		(* form -> base(b1) = base(a2) *)
		let query1 = [	(Boolean.mk_and ctx (formula_to_solver ctx form));
				(Boolean.mk_not ctx (Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [b1]) (Expr.mk_app ctx z3_names.base [a2])))
		] in		
		if (Solver.check solv query1)=SATISFIABLE 
			|| ((Solver.check solv (query_pvars a2))=UNSATISFIABLE) then AbstractionFail
		else
		(* the process continues as follows: Slseg on is unfolded and then similar process as folding of Hpointsto x Hpointsto is appplied *)
		try_add_slseg_to_pointsto ctx solv z3_names form i2 i1 pvars 1

	)
	(*| _ -> AbstractionFail*)

(* try list abstraction - first tries the last added, at least 2 predicates in
	sigma *)
let rec lseg_abstaction ctx solv z3_names form pvars =
	let rec f i j =
		(* Printf.printf "%d,%d\n" i j; *)
		let result = try_abstraction_to_lseg ctx solv z3_names form i j pvars in
		match result with
		| AbstractionApply new_form ->
			lseg_abstaction ctx solv z3_names new_form pvars
		| AbstractionFail -> (
			match i,j with
			| 1,_ -> form (* nothing change *)
			| _,0 -> f (i-1) (i-2)
			| _,_ -> f i (j-1)
		)
	in
	let n = List.length form.sigma in
	(* assert (n>1); *)
	if (n<2) then form else f (n-1) (n-2)


(***** Experiments *****)
(* let ptr_size=Exp.Const (Exp.Int (Int64.of_int 8))

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
    	BinOp ( Peq, UnOp ( Len, Var 1), Const (Int (Int64.of_int 16)));
        BinOp ( Peq, Var 2, UnOp ( Base, Var 2));
    	BinOp ( Peq, UnOp ( Len, Var 2), Const (Int (Int64.of_int 16)));
        ]
}

let form_abstr4 = {
    sigma = [ Hpointsto (Var 1,ptr_size, Var 2); Hpointsto(BinOp ( Pplus, Var 1, ptr_size),ptr_size, Var 10);
    	Hpointsto (Var 2,ptr_size, Var 3); Hpointsto (BinOp ( Pplus, Var 2, ptr_size),ptr_size, Var 10);
    	Hpointsto (Var 3,ptr_size, Var 4); Hpointsto (BinOp ( Pplus, Var 3, ptr_size),ptr_size, Var 10)];
    pi = [
    	BinOp ( Peq, Var 1, UnOp ( Base, Var 1));
    	BinOp ( Peq, UnOp ( Len, Var 1), Const (Int (Int64.of_int 16)));
        BinOp ( Peq, Var 2, UnOp ( Base, Var 2));
    	BinOp ( Peq, UnOp ( Len, Var 2), Const (Int (Int64.of_int 16)));
        BinOp ( Peq, Var 3, UnOp ( Base, Var 3));
    	BinOp ( Peq, UnOp ( Len, Var 3), Const (Int (Int64.of_int 16)));
        ]
}
let form_abstr5 = {
    sigma = [ Hpointsto (Var 1,ptr_size, Var 2); Hpointsto(BinOp ( Pplus, Var 1, ptr_size),ptr_size, Var 10);
    	Hpointsto(BinOp ( Pplus, Var 1, Exp.Const (Int (Int64.of_int 16))),ptr_size, Var 1);
    	Hpointsto (Var 2,ptr_size, Var 3); Hpointsto (BinOp ( Pplus, Var 2, ptr_size),ptr_size, Var 10);
    	Hpointsto(BinOp ( Pplus, Var 2, Exp.Const (Int (Int64.of_int 16))),ptr_size, Var 2)];
    pi = [
    	BinOp ( Peq, Var 1, UnOp ( Base, Var 1));
    	BinOp ( Peq, UnOp ( Len, Var 1), Const (Int (Int64.of_int 32)));
        BinOp ( Peq, Var 2, UnOp ( Base, Var 2));
    	BinOp ( Peq, UnOp ( Len, Var 2), Const (Int (Int64.of_int 32)));
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
    	BinOp ( Peq, UnOp ( Len, Var 1), Const (Int (Int64.of_int 16)));
    	BinOp ( Peq, Var 10, UnOp ( Base, Var 10));
        BinOp ( Peq, Var 2, UnOp ( Base, Var 2));
    	BinOp ( Peq, UnOp ( Len, Var 2), Const (Int (Int64.of_int 16)));
    	BinOp ( Peq, Var 11, UnOp ( Base, Var 11));
        ]
}
let form_abstr7 =
    let lambda= {param=[1;2] ;form={
      	sigma = [ Hpointsto (Var 1, ptr_size, Var 2) ]; pi=[] }}
    in
    {
    sigma = [ Hpointsto (Var 1,ptr_size, Var 2); Hpointsto(BinOp ( Pplus, Var 1, ptr_size),ptr_size, Var 10);
    	 Slseg (Var 10, Const (Ptr 0), lambda);
    	Hpointsto (Var 2,ptr_size, Var 3); Hpointsto (BinOp ( Pplus, Var 2, ptr_size),ptr_size, Var 11);
    	 Slseg (Var 11, Const (Ptr 0), lambda);
	];
    pi = [
    	BinOp ( Peq, Var 1, UnOp ( Base, Var 1));
    	BinOp ( Peq, UnOp ( Len, Var 1), Const (Int (Int64.of_int 16)));
        BinOp ( Peq, Var 2, UnOp ( Base, Var 2));
    	BinOp ( Peq, UnOp ( Len, Var 2), Const (Int (Int64.of_int 16)));
        ]
}
let form_abstr8 =
    {
    sigma = [ Hpointsto (Var 1,ptr_size, Var 2); Hpointsto(BinOp ( Pplus, Var 1, ptr_size),ptr_size, Var 10);
    	 Hpointsto (Var 10,ptr_size, Var 1); Hpointsto(BinOp ( Pplus, Var 10, ptr_size),ptr_size, Var 10);
    	Hpointsto (Var 2,ptr_size, Var 3); Hpointsto (BinOp ( Pplus, Var 2, ptr_size),ptr_size, Var 11);
    	 Hpointsto (Var 11,ptr_size, Var 2); Hpointsto(BinOp ( Pplus, Var 11, ptr_size),ptr_size, Var 11);
	];
    pi = [
    	BinOp ( Peq, Var 1, UnOp ( Base, Var 1));
    	BinOp ( Peq, UnOp ( Len, Var 1), Const (Int (Int64.of_int 16)));
    	BinOp ( Peq, Var 10, UnOp ( Base, Var 10));
    	BinOp ( Peq, UnOp ( Len, Var 10), Const (Int (Int64.of_int 16)));
        BinOp ( Peq, Var 2, UnOp ( Base, Var 2));
    	BinOp ( Peq, UnOp ( Len, Var 2), Const (Int (Int64.of_int 16)));
    	BinOp ( Peq, Var 11, UnOp ( Base, Var 11));
    	BinOp ( Peq, UnOp ( Len, Var 11), Const (Int (Int64.of_int 16)));
        ]
}

let form_abstr9 =
    let lambda= {param=[1;2] ;form={
      	sigma = [ Hpointsto (Var 1, ptr_size, Var 2) ]; pi=[] }}
    in
    {
    sigma = [  Slseg (Var 1, Var 2, lambda); Slseg (Var 2, Const (Ptr 0), lambda); Hpointsto (Var 3,ptr_size, Var 1);
	];
    pi = [BinOp ( Peq, Var 3, UnOp ( Base, Var 3));]
}

let form_abstr10 =
    let lambda= {param=[1;2] ;form={
      	sigma = [ Hpointsto (Var 1, ptr_size, Var 2) ]; pi=[BinOp ( Peq, Var 1, UnOp ( Base, Var 1));] }}
    in
    {
    sigma = [  Slseg (Var 1, Var 2, lambda); Slseg (Var 2, Const (Ptr 0), lambda); Hpointsto (Var 3,ptr_size, Var 1);
	];
    pi = [BinOp ( Peq, Var 3, UnOp ( Base, Var 3));]
}

let form_abstr11 =
    let lambda= {param=[1;2] ;form={
      	sigma = [ Hpointsto (Var 1, ptr_size, Var 2); Hpointsto(BinOp ( Pplus, Var 1, ptr_size),ptr_size, Var 10);
    	 Hpointsto (Var 10,ptr_size, Var 1); Hpointsto(BinOp ( Pplus, Var 10, ptr_size),ptr_size, Var 10);
	];
	pi=[BinOp ( Peq, Var 1, UnOp ( Base, Var 1));
	BinOp ( Peq, UnOp ( Len, Var 1), Const (Int (Int64.of_int 16)));
    	BinOp ( Peq, Var 10, UnOp ( Base, Var 10));
    	BinOp ( Peq, UnOp ( Len, Var 10), Const (Int (Int64.of_int 16)));
	] }}
    in
    {
    sigma = [  Slseg (Var 1, Var 2, lambda); Slseg (Var 2, Const (Ptr 0), lambda);
    	Hpointsto (Var 3,ptr_size, Var 1); Hpointsto(BinOp ( Pplus, Var 3, ptr_size),ptr_size, Var 10);
    	 Hpointsto (Var 10,ptr_size, Var 3); Hpointsto(BinOp ( Pplus, Var 10, ptr_size),ptr_size, Var 10);
	];
    pi = [BinOp ( Peq, Var 3, UnOp ( Base, Var 3));
    	BinOp ( Peq, UnOp ( Len, Var 3), Const (Int (Int64.of_int 16)));
    	BinOp ( Peq, Var 10, UnOp ( Base, Var 10));
    	BinOp ( Peq, UnOp ( Len, Var 10), Const (Int (Int64.of_int 16)));

    	]
}

let form_abstr12 =
    let lambda= {param=[1;2] ;form={
      	sigma = [ Hpointsto (Var 1, ptr_size, Var 2); Hpointsto(BinOp ( Pplus, Var 1, ptr_size),ptr_size, Var 10);
    	 Hpointsto (Var 10,ptr_size, Var 1); Hpointsto(BinOp ( Pplus, Var 10, ptr_size),ptr_size, Var 10);
	];
	pi=[BinOp ( Peq, Var 1, UnOp ( Base, Var 1));
	BinOp ( Peq, UnOp ( Len, Var 1), Const (Int (Int64.of_int 16)));
    	BinOp ( Peq, Var 10, UnOp ( Base, Var 10));
    	BinOp ( Peq, UnOp ( Len, Var 10), Const (Int (Int64.of_int 16)));
	] }}
    in
    {
    sigma = [  Slseg (Var 1, Var 2, lambda);
    	Hpointsto (Var 2,ptr_size, Var 3); Hpointsto(BinOp ( Pplus, Var 2, ptr_size),ptr_size, Var 10);
    	 Hpointsto (Var 10,ptr_size, Var 2); Hpointsto(BinOp ( Pplus, Var 10, ptr_size),ptr_size, Var 10);
	];
    pi = [BinOp ( Peq, Var 2, UnOp ( Base, Var 2));
    	BinOp ( Peq, UnOp ( Len, Var 2), Const (Int (Int64.of_int 16)));
    	BinOp ( Peq, Var 10, UnOp ( Base, Var 10));
    	BinOp ( Peq, UnOp ( Len, Var 10), Const (Int (Int64.of_int 16)));

    	]
}

let form_abstr13 =
    let lambda= {param=[1;2] ;form={
      	sigma = [ Hpointsto (Var 1, ptr_size, Var 2) ]; pi=[BinOp ( Peq, Var 1, UnOp ( Base, Var 1));] }}
    in
    {
    sigma = [  Slseg (Var 1, Var 2, lambda);  Hpointsto (Var 2,ptr_size, Var 3);
	];
    pi = [BinOp ( Peq, Var 2, UnOp ( Base, Var 2));]
}
 *)


(*
let x=match (try_pointsto_to_lseg ctx solv z3_names form_abstr2 0 2 []) with
| AbstractionApply x -> x;;

print_formula x;;
check_all_lambdas ctx solv x.sigma ;;

*)

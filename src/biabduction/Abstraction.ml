(*
 *  Copyright (C) Broom team
 *
 *  This file is part of Broom.
 *
 *  Broom is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  Broom is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <https://www.gnu.org/licenses/>.
 *)

open Formula
open Z3
open Z3wrapper

(* TODO: 
   (1) siplify pure part inside lambda and in the main formula after folding (i.e. get rid of useless existentials)
*)

exception ErrorInAbstraction of (string * Config.src_pos)

exception Get_eq_base_TO

(* since ocaml 4.12.0 there is __FUNCTION__ *)
let to_hpointsto_unsafe hpred = match hpred with
  | Slseg _ | Dlseg _ -> raise (Invalid_argument "to_hpointsto_unsafe: Received list instead of points-to")
  | Hpointsto (a,l,b) -> (a,l,b)

type res =
| AbstractionApply of Formula.t
| AbstractionFail

 
(* if the option is set to true, close the created lambdas *)
let lambda_close lambda =
	if Config.close_lambda ()
	then CloseLambda.close_lambda lambda
	else lambda


(* for a given pointer expression a1 find all spacial predicates with an equal base adress 
   include_a1=0 --- pointsto "a1 -> _" is skipped
   include_a1=1 --- pointsto "a1 -> _" is included
   skip --- a list of poinsto which are skipped within the test
   dir (in case of DLLs) -- 0: all, 1: from beginning, 2: from end (Hpointsto and Slseg are igneored)
*) 

(* in the case of solver timeout within get_eq_base, we raise an exception to avoid unsound result *)

let rec get_eq_base ctx solv z3_names form a1 index include_a1 skip dir =
	let ff = Boolean.mk_false ctx in
	if index=(List.length form.sigma) then []
	else
	if (List.mem index skip) 
	then  (get_eq_base ctx solv z3_names form  a1 (index+1) include_a1 skip dir)
	else
		let a2,a2end = match (List.nth form.sigma index) with
			| Hpointsto (a,_,_) -> (expr_to_solver_only_exp ctx z3_names a),ff
			| Slseg (a,_,_,_) -> (expr_to_solver_only_exp ctx z3_names a),ff
			| Dlseg (a,_,b,_,_) -> (expr_to_solver_only_exp ctx z3_names a),(expr_to_solver_only_exp ctx z3_names b)
		in
		(* form -> base(a1) = base(a2) *)
		let query=[ 
			(Boolean.mk_not ctx (Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [a1]) (Expr.mk_app ctx z3_names.base [a2])))
		] in
		let query_res=
			if (dir=2) 
			then false 
			else (
				match (Solver.check solv query) with
				| UNSATISFIABLE -> true
				| SATISFIABLE -> false
				| _ -> raise Get_eq_base_TO
			)
		in
		(* form -> base(a1) = base(a2end) *)
		let queryend=if a2end=ff then [ff] else
			[ 
			(Boolean.mk_not ctx (Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [a1]) (Expr.mk_app ctx z3_names.base [a2end])))
		] in
		let queryend_res= 
			if ((a2end=ff) || (dir=1)) 
			then false 
			else (
				match (Solver.check solv queryend) with
				| UNSATISFIABLE -> true
				| SATISFIABLE -> false
				| _ -> raise Get_eq_base_TO
			)
		in
		(* form -> a1 != a2 *)
		let query2= [ 
			(Boolean.mk_not ctx (Boolean.mk_not ctx (Boolean.mk_eq ctx a1 a2)))
		] in
		let query2_res= 
			if ((dir=2)||(include_a1=1)) 
			then true 
			else (
				match (Solver.check solv query2) with
				| UNSATISFIABLE -> true
				| SATISFIABLE -> false
				| _ -> raise Get_eq_base_TO
			)
		in
		(* form -> a1 != a2end *)
		let query2end=if a2end=ff then [ff] else
			[  
			(Boolean.mk_not ctx (Boolean.mk_not ctx (Boolean.mk_eq ctx a1 a2end)))
		] in
		let query2end_res= 
			if (include_a1=1 || a2end=ff || dir=1) 
			then true 
			else (
				match (Solver.check solv query2end) with
				| UNSATISFIABLE -> true
				| SATISFIABLE -> false
				| _ -> raise Get_eq_base_TO
			)
		in
		match query_res,query2_res,queryend_res, query2end_res with 
		| true, true, _,_ -> index :: (get_eq_base ctx solv z3_names form  a1 (index+1) include_a1 skip dir)
		| false, _, true, true -> index :: (get_eq_base ctx solv z3_names form  a1 (index+1) include_a1 skip dir)
		| _ -> (get_eq_base ctx solv z3_names form  a1 (index+1) include_a1 skip dir)


(* Check that points-to on i1 and i2 can have (=SAT) equal distance from base of the block *)
let check_eq_dist_from_base ctx solv z3_names form i1 i2 =
	let ff = Boolean.mk_false ctx in
	let get_src_and_len i = 
		match (List.nth form.sigma i) with
			| Slseg _ -> ff,ff
			| Dlseg _ -> ff,ff
			| Hpointsto (a,l,_) -> (expr_to_solver_only_exp ctx z3_names a),(expr_to_solver_only_exp ctx z3_names l)
	in
	let a1,l1 = get_src_and_len i1 in
	let a2, l2 = get_src_and_len i2 in
	if ((a1=ff) || (a2=ff)) then false
	else
		(* SAT: form /\ a1-base(a1) = a2 - base(a2) *)
		let query1 = [ 
			Boolean.mk_eq ctx 
				(BitVector.mk_sub ctx  a1 (Expr.mk_app ctx z3_names.base [a1]) )
				(BitVector.mk_sub ctx  a2 (Expr.mk_app ctx z3_names.base [a2]) )
		] in
		(* SAT l1=l2 *)
		let query2 = [
			Boolean.mk_eq ctx l1 l2
		] in

		((Solver.check solv query1)=SATISFIABLE)&&((Solver.check solv query2)=SATISFIABLE)


(* The input is a formula and two lists of indexes to form.sigma,
  the goal is to create a list of tuples (a,b) such that pointsto predicates on position a and b has equal distance from 
  base of particular blocks *)
type match_res =
| MatchOK of (int * int) list
| MatchFail


(* checks that the the fields of the two blocks are at the same offset, returns pairs of fields with same offset in block *)
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


(* Check that for variables v1 and v2 there exists a triple (base1,base2,_) in block_bases s.t.
   (1) form -> base(base1) = base(v1) /\ base(base2) = base(v2)
   (2) SAT: form /\ v1-base(v1) = v2 - base(v2)
   *)
let rec check_block_bases ctx solv z3_names form v1 v2 block_bases =
	match block_bases with
	| [] -> false
	| (b1,b2,_)::rest ->
		let var1=expr_to_solver_only_exp ctx z3_names (Exp.Var v1) in
		let var2=expr_to_solver_only_exp ctx z3_names (Exp.Var v2) in
		(* form -> base(base1) = base(v1) /\ base(base2) = base(v2) *)
		let query_blocks=[ 
			(Boolean.mk_not ctx (Boolean.mk_and ctx [
				(Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [b1]) (Expr.mk_app ctx z3_names.base [var1]));
				(Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [b2]) (Expr.mk_app ctx z3_names.base [var2]))
			]))
		] in
		(* SAT: form /\ v1-base(v1) = v2 - base(v2) *)
		let query_dist = [
				Boolean.mk_eq ctx 
				(BitVector.mk_sub ctx  var1 (Expr.mk_app ctx z3_names.base [var1]) )
				(BitVector.mk_sub ctx  var2 (Expr.mk_app ctx z3_names.base [var2]) )
		] in

		if ((Solver.check solv query_blocks)=UNSATISFIABLE)&&((Solver.check solv query_dist)=SATISFIABLE) then true
		else check_block_bases ctx solv z3_names form v1 v2 rest

(* check that v1 and v2 are back links in Dlseg with the use of block bases --->
   1) there exists (b1,b2,1) in block bases such that base(v2)=base(b1)
   2) forall (b1,b2,_) in block bases (base(v1)!=base(b1) /\ base(v1)!=base(v2)) is SAT
*)
let rec check_backlink ctx solv z3_names form v2 block_bases =
	match block_bases with 
	| [] -> false,[]
	| (b1,b2, flag)::rest ->
		let query_backlink=[ 
			(Boolean.mk_not ctx 
				(Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [b1]) (Expr.mk_app ctx z3_names.base [v2]));
			)
		] in
		match flag,(check_backlink ctx solv z3_names form  v2 rest) with
		| 1,(false,base_list) ->
			(if ((Solver.check solv query_backlink)=UNSATISFIABLE) 
			then true,[b2]@base_list
			else false,[b1;b2]@base_list
			)
		| _,(false,base_list) ->  false,[b1;b2]@base_list (* backlink found, no need to query the solver *)
		| _,(true,base_list) ->  true,[b1;b2]@base_list (* backlink found, no need to query the solver *)



let check_dlseg_from_block_bases ctx solv z3_names form v1 v2 block_bases =
	match (check_backlink ctx solv z3_names form v2 block_bases) with
	| false,_ -> false
	| true, base_list ->
		let non_eq b = (Boolean.mk_not ctx 
				(Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [b]) (Expr.mk_app ctx z3_names.base [v1]));
			)
		in
		let query_nomem =(List.map non_eq base_list) in
		if ((Solver.check solv query_nomem)=SATISFIABLE) then true else false

(* This is called in the case that there is no allocated block before the DLL candidate *)
let check_backlink_simplified ctx solv z3_names form i2 block_bases =
	match (List.nth form.sigma i2) with
	| Hpointsto (aa,_,_) ->
		let a2 = (expr_to_solver_only_exp ctx z3_names aa) in
		(match (check_backlink ctx solv z3_names form a2 block_bases) with
			| (x,_) -> x
		)
	| _ -> false 
	

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
(* heap_pred is Hpointsto predicate, 5th param indicates shared pointers*)
| CheckOK of (int * int * heap_pred * int * bool) list 
| DlsegBackLink
| CheckFail

(* for testing *)
let rec quintuples_to_string quintuples =
	match quintuples with
	(a,b,points_to,is_dls,is_shared) :: tail -> "(" ^ (string_of_int a) ^ "," ^ 
		(string_of_int b) ^ "," ^ Formula.points_to_to_string points_to ^ "," ^ 
		(string_of_int is_dls) ^ "," ^ (string_of_bool is_shared) ^ "), " ^
		 quintuples_to_string tail 
	| [] -> "\n"

(* this function is quite similar to the try_pointsto_to_lseg, but is is dedicated to the blocks referenced from the blocks, which should be folded *)
let rec find_ref_blocks ctx solv z3_names form i1 i2 block_bases gvars=
	let global_bases base g=Boolean.mk_not ctx
		(Boolean.mk_eq ctx
			(Expr.mk_app ctx z3_names.base [base]) 
			(Expr.mk_app ctx z3_names.base [(expr_to_solver_only_exp ctx z3_names (Exp.Var g))])
		)
	in
	match (List.nth form.sigma i1), (List.nth form.sigma i2) with
	| Hpointsto (a,l,_), Hpointsto (aa,ll,_) ->
		let a1,l1 = (expr_to_solver_only_exp ctx z3_names a),(expr_to_solver_only_exp ctx z3_names l) in
		let a2,l2 = (expr_to_solver_only_exp ctx z3_names aa),(expr_to_solver_only_exp ctx z3_names ll) in
		(* form ->  l1 = l2 *)
		let query1 = [	
			(Boolean.mk_not ctx (Boolean.mk_eq ctx l1 l2));
		] in
		(* SAT: form /\ base(a1) != base(a2) /\ a1-base(a1) = a2 - base(a2) *)
		let query2 = [ 
			Boolean.mk_eq ctx 
			(BitVector.mk_sub ctx  a1 (Expr.mk_app ctx z3_names.base [a1]) )
			(BitVector.mk_sub ctx  a2 (Expr.mk_app ctx z3_names.base [a2]) )
		] in
		if not (((Solver.check solv query1)=UNSATISFIABLE)
			&& ((Solver.check solv query2)=SATISFIABLE)) then  CheckFail
		else
		if (check_dlseg_from_block_bases ctx solv z3_names form a1 a2 block_bases)
		then DlsegBackLink
		else
		(* SAT: forall g in gvar. base(g)!=base(a1) /\ base(g)!=base(a2) *)
		(* ensures that pvars are not abstracted *)
		let query3=if gvars=[] then []
			else
			[ 
				Boolean.mk_and ctx (List.map (global_bases a1) gvars);
				Boolean.mk_and ctx (List.map (global_bases a2) gvars);] 
		in
		if not ((Solver.check solv query3)=SATISFIABLE) then CheckFail
		else
		(* check all pointsto with equal bases to a1/a2 *)
		let a1_block=get_eq_base ctx solv z3_names form a1 0 1 [] 0 in
		let a2_block=get_eq_base ctx solv z3_names form a2 0 1 [] 0 in
		(match match_pointsto_from_two_blocks ctx solv z3_names form a1_block a2_block with
			| MatchFail -> CheckFail
			| MatchOK matchres ->  
				(match (check_matched_pointsto ctx solv z3_names form matchres ((a1,a2,0)::block_bases) 0 gvars) with
					| CheckOK checked_matchres -> CheckOK  checked_matchres
					| CheckFail  -> CheckFail
					| DlsegBackLink -> raise_notrace (ErrorInAbstraction ("DllBackling is not expected here",__POS__))
				)
		)
	| Slseg(a1,b1,l1,shared1), Slseg(a2,b2,l2,_) -> ( 
		let vars_b1 = find_vars_expr b1 in
		let vars_b2 = find_vars_expr b2 in
		let eq_base var = get_eq_base ctx solv z3_names form  (expr_to_solver_only_exp ctx z3_names (Exp.Var var)) 0 1 [] 0 in
		let pt_refs_b1 = List.concat(List.map eq_base vars_b1) in 
		let pt_refs_b2 = List.concat(List.map eq_base vars_b2) in
		let query=[
				Boolean.mk_eq ctx (expr_to_solver_only_exp ctx z3_names b1) (expr_to_solver_only_exp ctx z3_names b2)
			] in
		(* check entailment between l1 and l2
		   we use a fresh solver, because the current one is used in incremental way for solving the Abstraction queries *)
		let entailment_res=Abduction.check_lambda_entailment (config_solver ()) l1 l2 0 in
		if entailment_res=0 then CheckFail
		else
		let new_lambda=if (entailment_res=1) then l2 else l1 in
		(* check that a1 and a2 are not is equal base with a global variable *)
		(* SAT: forall g in gvar. base(g)!=base(a1) /\ base(g)!=base(a2) *)
		let query3=if gvars=[] then []
			else
			[ 
				Boolean.mk_and ctx (List.map (global_bases (expr_to_solver_only_exp ctx z3_names a1)) gvars);
				Boolean.mk_and ctx (List.map (global_bases (expr_to_solver_only_exp ctx z3_names a2)) gvars);] 
		in
		if ((Solver.check solv query3)=UNSATISFIABLE) then CheckFail
		else
		(* check compatibility of b1 and b2 *)
		(*DAVID TODO: passed shared1 argument to newly created Slseg when introducing first param in Slseg*)
		match vars_b1, vars_b2, pt_refs_b1, pt_refs_b2 with
		| _,_,[],[] -> (* there is no referenced predicate in sigma by b1 and b2  -> check sat *)
			if (Solver.check solv query)=SATISFIABLE then CheckOK [(i1,i2,Slseg(a1,b1,new_lambda,shared1),0, false)]
			else CheckOK [(i1,i2,Slseg(a1,Undef,new_lambda,shared1),0, false)]
		| [x1],[x2],_::_,_::_ -> (* b1 and b2 refers to a predicate in sigma *) 
			if (check_block_bases ctx solv z3_names form x1 x2 
				((expr_to_solver_only_exp ctx z3_names a1,expr_to_solver_only_exp ctx z3_names a2,0 )::block_bases)) 
			then CheckOK [(i1,i2,Slseg(a1,b1,new_lambda,shared1),0,false)]
			else CheckFail
		
		| _ -> CheckFail
		)
	| Dlseg(a1,b1,c1,d1,l1), Dlseg(a2,b2,c2,d2,l2) -> ( 
		let vars_b1 = find_vars_expr b1 in
		let vars_b2 = find_vars_expr b2 in
		let vars_d1 = find_vars_expr d1 in
		let vars_d2 = find_vars_expr d2 in
		let eq_base var = get_eq_base ctx solv z3_names form  (expr_to_solver_only_exp ctx z3_names (Exp.Var var)) 0 1 [] 0 in
		let pt_refs_b1 = List.concat(List.map eq_base vars_b1) in 
		let pt_refs_b2 = List.concat(List.map eq_base vars_b2) in
		let pt_refs_d1 = List.concat(List.map eq_base vars_d1) in 
		let pt_refs_d2 = List.concat(List.map eq_base vars_d2) in
		let queryB=[
				Boolean.mk_eq ctx (expr_to_solver_only_exp ctx z3_names b1) (expr_to_solver_only_exp ctx z3_names b2)
			] in
		let queryD=[
				Boolean.mk_eq ctx (expr_to_solver_only_exp ctx z3_names d1) (expr_to_solver_only_exp ctx z3_names d2)
			] in
		(* check entailment between l1 and l2 *)
		(* we use a fresh solver, because the current one is used in incremental way for solving the Abstraction queries *)
		let entailment_res=Abduction.check_lambda_entailment (config_solver ()) l1 l2 0 in
		if entailment_res=0 then CheckFail
		else
		let new_lambda=if (entailment_res=1) then l2 else l1 in
		(* check that a1 and a2 are not is equal base with a global variable *)
		(* SAT: forall g in gvar. base(g)!=base(a1) /\ base(g)!=base(a2) /\  base(g)!=base(c1) /\ base(g)!=base(c2)*)
		let query3=if gvars=[] then []
			else
			[ 
				Boolean.mk_and ctx (List.map (global_bases (expr_to_solver_only_exp ctx z3_names a1)) gvars);
				Boolean.mk_and ctx (List.map (global_bases (expr_to_solver_only_exp ctx z3_names a2)) gvars);
				Boolean.mk_and ctx (List.map (global_bases (expr_to_solver_only_exp ctx z3_names c1)) gvars);
				Boolean.mk_and ctx (List.map (global_bases (expr_to_solver_only_exp ctx z3_names c2)) gvars);] 
		in
		if ((Solver.check solv query3)=UNSATISFIABLE) then CheckFail
		else
		(* check compatibility of b1 ~ b2 and d1 ~ d2 *) (* !!! To be finished !!! *)
		let exp_false=Exp.Const (Bool false) in
		let new_b =
			match vars_b1, vars_b2, pt_refs_b1, pt_refs_b2 with
			| _,_,[],[] -> (* there is no referenced predicate in sigma by b1 and b2  -> check sat *)
				if (Solver.check solv queryB)=SATISFIABLE then b1 else Undef
			| [x1],[x2],_::_,_::_ -> (* b1 and b2 refers to a predicate in sigma *)
				if (check_block_bases ctx solv z3_names form x1 x2 
				([expr_to_solver_only_exp ctx z3_names a1,expr_to_solver_only_exp ctx z3_names a2,0;
				  expr_to_solver_only_exp ctx z3_names c1,expr_to_solver_only_exp ctx z3_names c2,0]@block_bases))
				then b1 else exp_false
			| _ -> exp_false	
		in
		let new_d =
			match vars_d1, vars_d2, pt_refs_d1, pt_refs_d2 with
			| _,_,[],[] -> (* there is no referenced predicate in sigma by b1 and b2  -> check sat *)
				if (Solver.check solv queryD)=SATISFIABLE then d1 else Undef
			| [x1],[x2],_::_,_::_ -> (* b1 and b2 refers to a predicate in sigma *)
				if (check_block_bases ctx solv z3_names form x1 x2 
				([expr_to_solver_only_exp ctx z3_names a1,expr_to_solver_only_exp ctx z3_names a2,0;
				  expr_to_solver_only_exp ctx z3_names c1,expr_to_solver_only_exp ctx z3_names c2,0]@block_bases))
				then d1 else exp_false
			| _ -> exp_false	
		in
		if (new_b=exp_false) || (new_d=exp_false) then CheckFail
		else CheckOK [(i1,i2,Dlseg(a1,new_b,c1,new_d,new_lambda),0, false)]
		)
	| _ -> CheckFail (* Slseg can not be matched with Hpointsto *)

(* recursion of nested sublists is supported up to one level -> to identify nested lists of nested lists,
	 several steps of abstractions have to be performed*)
(* returns quintuples (a,b,l,d,s) where a and b are indices of the matched fields in form.sigma, 
	 l is lambda, d == 0 marks sls and d == 1 or d == 2 marks dls, s indicates whether l is shared*)
and check_matched_pointsto ctx solv z3_names form pairs_of_pto block_bases incl_ref_blocks gvars=
	match pairs_of_pto with
	| [] -> CheckOK []
	| (i1,i2)::rest ->
		(* auxiliary function iterating through 'pairs_of_pto' *)
		let check_subsequent_pair block_bases_n new_quintuples= 
			match check_matched_pointsto ctx solv z3_names form rest block_bases_n incl_ref_blocks gvars with
			| CheckFail -> CheckFail
			| CheckOK res -> CheckOK(new_quintuples @ res)
			| DlsegBackLink -> raise_notrace (ErrorInAbstraction ("DllBackling is not expected here",__POS__))

		in
		(* Slseg can not present here *)
		let a1,s1,b1 = to_hpointsto_unsafe (List.nth form.sigma i1) in
		let a2,_,b2 =  to_hpointsto_unsafe (List.nth form.sigma i2) in
		let vars_b1 = find_vars_expr b1 in (* vars_b1/vars_b1 should contain only one element*)
		let vars_b2 = find_vars_expr b2 in
		let eq_base dir var = get_eq_base ctx solv z3_names form  (expr_to_solver_only_exp ctx z3_names (Exp.Var var)) 0 1 [] dir in
		let pt_refs_b1 = List.concat(List.map (eq_base 1) vars_b1) in 
		let pt_refs_b2 = List.concat(List.map (eq_base 1) vars_b2) in
		let pt_refs_b1_back = List.concat(List.map (eq_base 2) vars_b1) in 
		let pt_refs_b2_back = List.concat(List.map (eq_base 2) vars_b2) in
		(* query checks if pointer's dest fields are equal *)
		let query_eq=[
				Boolean.mk_not ctx 
					(Boolean.mk_eq ctx 
					(expr_to_solver_only_exp ctx z3_names b1) 
					(expr_to_solver_only_exp ctx z3_names b2))
			] in
		let eq_b1_b2 = Solver.check solv query_eq=UNSATISFIABLE in
		(* check that the pointers lead back to the same block, lead to a new block or also 
		 lead to the next block*)
		(* pt_refs_b1/pt_refs_b2 collect all indices in form.sigma of points-to predicates 
		 with source = b1/b2 in ascending order*)
		match vars_b1, vars_b2, pt_refs_b1, pt_refs_b2, pt_refs_b1_back,pt_refs_b2_back  with
		| _,_,[],[],[],[] -> 
			(* b1 and b2 does not points to an fixed allocated block --- i.e. only integers or undef *) 
			let value = if eq_b1_b2 then b1 else Undef 
			in check_subsequent_pair block_bases [(i1,i2, Hpointsto (a1,s1,value),0,false)]
		| [x1],[x2],f1::_,f2::_,[],[] 
		| [x1],[x2],[],[],f1::_,f2::_ ->
			(* cover cases where pointers lead back to same block or where pointers both point to new blocks*)
			(* b1 and b2 contaisn only a single variable pointing to an allocated block *)
			(match (check_block_bases ctx solv z3_names form x1 x2 block_bases), incl_ref_blocks with
			(* check_block_bases checks if b1 and b2 are in the same block as a1/a2 and have same offset 
			-> pointers pointing back to node struct*)
			| true, _ ->
				check_subsequent_pair block_bases [(i1,i2,(List.nth form.sigma i1),0,false)]
				(* 'false' means that dest of b1 and b2 are not known to be comparable*)
			| false, 0 -> CheckFail
			| false, _ -> 
				if eq_b1_b2 then
				 	check_subsequent_pair block_bases [(i1,i2,List.nth form.sigma i1,0,true)]
				else	 
					(match (find_ref_blocks ctx solv z3_names form f1 f2 block_bases gvars) with
					| CheckFail -> CheckFail
					(* this case corresponds to a nested list where you try to match sublists*)

					| CheckOK res_rec ->
						check_subsequent_pair ((expr_to_solver_only_exp ctx z3_names a1,expr_to_solver_only_exp ctx z3_names a2,0 )::block_bases)
							((i1,i2,(List.nth form.sigma i1),0, false) :: res_rec) 
						(* case where you construct DLS*)
					| DlsegBackLink -> check_subsequent_pair block_bases [(i1,i2,(List.nth form.sigma i1),1, false)]
					)
			)
		| _,[_],[],f2::_,[],[] -> (* Backlink of the Dlseg folding, where the backlink of the first segment does not points-to 
						an alocated block *)
			(match (check_backlink_simplified ctx solv z3_names form f2 block_bases),
				(check_matched_pointsto ctx solv z3_names form rest block_bases incl_ref_blocks gvars) with
					| true, CheckOK res -> CheckOK ((i1,i2,(List.nth form.sigma i1),2,false):: res )
					| _ -> CheckFail
					)
		| _,[_],[],f2::_,_,[] -> (* Used within  try_add_lseg_to_pointsto flag=2:
						Dlseg(x,_,endlist,y) * Hpointsto (y,z) [1] * Hpointsto (y,endlist) [2] -> Dlseg(x,_,y,z). 
						The Dlseg in by the try_add_lseg_to_pointsto function  unfolded into 
						Dlseg(x,_,z,endlist) [3] * Hpointsto(endlist,y) [4] * Hpointsto(endlist,z) [5]
						and Ptrefs_b2=[4,5] and Ptrefs_b1=[] and Ptrefs_b1_back [3] *) 
			(match (check_backlink_simplified ctx solv z3_names form f2 block_bases),
				(check_matched_pointsto ctx solv z3_names form rest block_bases incl_ref_blocks gvars) with
					| true, CheckOK res -> CheckOK ((i1,i2,(List.nth form.sigma i1),1, false):: res )
					| _ -> CheckFail
					)


		| _ ->
			(* complicated pattern -> stop abstraction *)
			Config.debug2 ">>> abstraction failed - complicated pattern"; CheckFail

(* auxiliary functions for folding *)			
let rec get_backlinks quintuples res =
	match quintuples with
	| [] -> res
	| (y1,y2,_,i,_)::rest -> 
		match i,res with
		| 0,_ -> get_backlinks rest res
		| _,(-1,-1) -> get_backlinks rest (y1,y2)
		| _ -> (-2,-2) (* more then a single backlink *)

let rec get_indeces quintuples =
	match quintuples with
	| [] -> [],[]
	| (a,b,_,_,_)::rest -> 
		match get_indeces rest with
		| a1,a2 -> (a::a1,b::a2)

	(* lambda may be overaproximated during the matches *)
let rec get_fresh_var s confl=
   if (List.mem s confl)
    then get_fresh_var (s+1) confl
	else s

(* returns tuples of form (l,bl,sv,se) where 'l' is the lambda obtained from all quintuples,
 'bl' is the new backlink variable, 'sv' are the new shared variables 
 (to be placed into lambda.param), 'se' are the shared expressions 
 (to be placed into Slseg's 4th param), so 'List.length sv = List.length se' holds) *)
let rec new_lambda_from_quintuples quintuples form =
	match quintuples with 
	| [] -> [],-1, [], []
	| (_,index,lambda,2,_)::rest -> 
		let (_,_,c)=to_hpointsto_unsafe(List.nth form.sigma index) in
		let (a,b,_)=to_hpointsto_unsafe(lambda) in
		let lambda_rest,_,shared_exprs_rest, shared_vars_rest =new_lambda_from_quintuples rest form in
		let fresh_backlink_var = get_fresh_var 1 (find_vars form @ shared_vars_rest) in 
		let c_new=substitute_expr (Exp.Var fresh_backlink_var) (Exp.Var (List.nth (find_vars_expr c) 0)) c in
		(Hpointsto (a,b,c_new) :: lambda_rest), fresh_backlink_var, shared_exprs_rest,shared_vars_rest
	| (_,_,lambda,_,is_shared)::rest -> 
		let lambda_rest,new_backlink_var, shared_exprs_rest, shared_vars_rest = new_lambda_from_quintuples rest form in
		let new_lamba, new_shared_exprs, new_shared_vars = 
		if is_shared then 
			let src,l,shared_expr = to_hpointsto_unsafe(lambda) in 
			let fresh_var = get_fresh_var 1 (new_backlink_var :: (find_vars form) @ shared_vars_rest) in
			Hpointsto(src,l,Var fresh_var), [shared_expr], [fresh_var]
		else
			lambda, [], [] 
		in
		(new_lamba :: lambda_rest), new_backlink_var, new_shared_exprs @ shared_exprs_rest, new_shared_vars @ shared_vars_rest	

(* fold the pointsto into a existing list segment using the unfolded version of the slseg *)
let fold_pointsto_slseg solver form i2_orig unfolded_form new_i1 new_i2 res_quintuples flag =
	let y1,y2=get_backlinks res_quintuples (-1,-1) in
	if y1=(-2) then AbstractionFail (* more then a single backlink *)
	else
	let rec range i j = if i > j then [] else i :: (range (i+1) j) in
	let i_unfolded_slseg=(List.length unfolded_form.sigma)-1 in (* index of the partially unfolded lseg *)
	let tmp1,tmp2=get_indeces res_quintuples in
	(* new_i2 :: tmp2 (resp. new_i1 :: tmp1) must contain all inceces from (List.length form.sigma)-1 to (List.length unfolded_form.sigma)-2 *)
	let indeces_to_check=
		match flag with
		| 0 -> (new_i2 :: tmp2) (* the indeces of unfolded part of the predicate are new_i2:: tmp2 *)
		| 1| 2 ->  (new_i1 :: tmp1) (* flag 2 --> the unfolded DLL has indeces new_i1 :: tmp1 *)
		| _ -> raise_notrace (ErrorInAbstraction ("BAD flag",__POS__))
	in
	if not (List.sort compare indeces_to_check = range ((List.length form.sigma)-1) (i_unfolded_slseg-1))
	then raise_notrace (ErrorInAbstraction ("BAD indeces",__POS__))  (* AbstractionFail *)
	else
	let nomem l x = not (List.mem x l) in
	(* indeces to be removed from unfolded_form *)
	let to_remove=[new_i1;new_i2]@tmp1@tmp2@[i_unfolded_slseg] in
	let rec get_new_sigma i=
		if i=(List.length unfolded_form.sigma) then []
		else if (List.mem i to_remove) then get_new_sigma (i+1)
		else (List.nth unfolded_form.sigma i) :: get_new_sigma (i+1)
	in 
	let get_new_lambda,dll_backlink, shared_exprs, shared_vars=
		let new_l,new_back_link_var, shared_exprs, shared_vars= new_lambda_from_quintuples res_quintuples unfolded_form in
		match (List.nth unfolded_form.sigma new_i1) with
		| Hpointsto (a,l,b) ->(
			match (find_vars_expr b) with
			| _::[] -> (Hpointsto (a,l,b) ::new_l),new_back_link_var, shared_exprs, shared_vars
			| _ -> (Hpointsto (a,l,Exp.Var (get_fresh_var (new_back_link_var+1) (find_vars unfolded_form))) 
				::new_l), new_back_link_var, shared_exprs, shared_vars (* change null/undef or equations for fresch variable *)
			)
		| _ -> raise_notrace (ErrorInAbstraction ("Something bad happened, probably broken unfolding",__POS__)) (*[]*)
	in
	(* get the parameters of the list segment *)
	let pto_a,pto_b,pto_b_expr,pto_a_expr = match (List.nth unfolded_form.sigma new_i1) with
			| Hpointsto (a,_,b) -> (find_vars_expr a),  (find_vars_expr b), b, a
			| _ -> raise_notrace (ErrorInAbstraction ("Expecting pointsto",__POS__))
	in
	let pto_a2,pto_b2 = match (List.nth unfolded_form.sigma new_i2) with
			| Hpointsto (a,_,b) -> ( 
				let offset=try_simplify_SL_expr_to_int solver  form (Exp.BinOp (Pminus,a,pto_b_expr)) in
				match offset with
				| None -> [],[]
				| Some 0L -> (find_vars_expr a), [b]
				| Some i -> (find_vars_expr a), [Exp.BinOp (Pplus,b,Const (Int i))]
				)

			| _ -> raise_notrace (ErrorInAbstraction ("Expecting pointsto",__POS__))
	in
	let y2_dest_expr= if y2<0 then Exp.Undef
		else match (List.nth unfolded_form.sigma y2) with
			|  Hpointsto (_,_,b) -> b
			| _ -> raise_notrace (ErrorInAbstraction ("Expecting pointsto",__POS__))
	in
	let pto_back_b,dll_backlink = if y1<0 then [],[]
		else 
			let offset=try_simplify_SL_expr_to_int solver  form (Exp.BinOp (Pminus,pto_a_expr,y2_dest_expr)) in
			match (List.nth unfolded_form.sigma y1),dll_backlink,offset with
			(* HERE: we should add offset  adjustment*)
			| Hpointsto (_,_,b),-1, Some 0L -> [b],(find_vars_expr b)
			| Hpointsto (_,_,b),-1, Some i -> [Exp.BinOp (Pplus,b,Const (Int i))],(find_vars_expr b)
			|  Hpointsto (_,_,b),back_l, Some 0L -> [b], [back_l]
			|  Hpointsto (_,_,b),back_l, Some i -> [Exp.BinOp (Pplus,b,Const (Int i))], [back_l]
			| _ -> raise_notrace (ErrorInAbstraction ("Expecting pointsto",__POS__))
	in
	let lseg_d,lambda = match (List.nth unfolded_form.sigma i_unfolded_slseg) with
			| Hpointsto _ -> raise_notrace (ErrorInAbstraction ("Points-to can not be on this place",__POS__))
			| Slseg (_,d,lambda,_) -> [d],lambda
			| Dlseg (_,_,_,d,lambda) -> [d],lambda
	in
	let lseg_a_orig,lseg_b_orig,lseg_c_orig,lseg_d_orig,lambda_orig = match (List.nth form.sigma i2_orig) with
			| Hpointsto _ -> raise_notrace (ErrorInAbstraction ("Points-to can not be on this place",__POS__));
			| Slseg (a,d,lambda,_) -> (find_vars_expr a),[],[],[d],lambda
			| Dlseg (a,b,c,d,lambda) -> (find_vars_expr a),[b],(find_vars_expr c),[d],lambda
	in
	(* this is a safety check that unfolding works correctly. *)
	if not (((lseg_d=lseg_d_orig)||flag=2) && (lambda=lambda_orig) ) 
	then raise_notrace (ErrorInAbstraction ("Something bad with unfolding",__POS__)) (*AbstractionFail*)
	else
	let p1,p2,p3,p4,p1_lambda,p2_lambda,p3_lambda=
		match flag with
		| 0 -> pto_a,pto_back_b,lseg_c_orig,lseg_d,pto_a,lseg_a_orig,dll_backlink
		| 1 -> lseg_a_orig,[],[],pto_b2,pto_a,pto_b,[]
		| 2 -> lseg_a_orig,lseg_b_orig,pto_a2,pto_b2,pto_a,pto_a2,dll_backlink
		| _ -> raise_notrace (ErrorInAbstraction ("Flag is different from 0,1,2",__POS__))
	in
	match p1,p2,p3,p4,p1_lambda,p2_lambda,p3_lambda,y1 with
	| [a],_,_,[d],[a_lambda],[b_lambda],_,-1 -> (*Slseg*)
		let lambda={param=[a_lambda;b_lambda] @ shared_vars; 
			form=(simplify  {pi=unfolded_form.pi; sigma=get_new_lambda} (List.filter (nomem [a_lambda;b_lambda]) (find_vars unfolded_form)))
		} in
		AbstractionApply {pi=unfolded_form.pi; sigma=(get_new_sigma 0) @ [Slseg (Exp.Var a, d, (lambda_close lambda),shared_exprs)]}
	| [a],[b],[c],[d],[a_lambda],[b_lambda],[c_lambda],_ -> (*Dlseg*)
		let lambda={param=[a_lambda;b_lambda;c_lambda]; 
			form=(simplify  {pi=unfolded_form.pi; sigma=get_new_lambda} (List.filter (nomem [a_lambda;b_lambda;c_lambda]) (find_vars unfolded_form)))
		} in
		AbstractionApply {pi=unfolded_form.pi; sigma=(get_new_sigma 0) @ [Dlseg (Exp.Var a, b, Exp.Var c, d, (lambda_close lambda))]}
	| _ -> AbstractionFail
	

(* fold the pointsto on indeces i1 and i2 with its neighborhood given by the list of quadruples of the type check_res,
  each quadruple consist of two indeces, a spacial predicated (which should be placed into the lambda) and flag whether it is a backlink *)
let fold_pointsto ctx solv z3_names form i1 i2 res_quintuples =
	let y1,y2=get_backlinks res_quintuples (-1,-1) in
	if y1=(-2) then AbstractionFail (* more then a single backlink *)
	else
	(* first, get only the first two elements from the triples  and store it into the tmp1, and tmp2*)
	let tmp1,tmp2=get_indeces res_quintuples in
	let neighbours= [i1;i2] @ tmp1 @ tmp2 in
	let nomem l x = not (List.mem x l) in
	(* get_new_sigma is used to determine which formulas in the new sigma have to be retained and which are abstracted *)
	let rec get_new_sigma i=
		if i=(List.length form.sigma) then []
		else if (List.mem i neighbours) then get_new_sigma (i+1)
		else (List.nth form.sigma i) :: get_new_sigma (i+1)
	in
	(* lambda may be overaproximated during the matches *)
	let new_lambda_incomplete, dll_backlink, shared_exprs, shared_vars = new_lambda_from_quintuples res_quintuples form in 
	let new_lambda = (List.nth form.sigma i1):: new_lambda_incomplete in
	(* get the parameters of the list segment *)
	let p1,p1_z3,p1_dest_expr,p1_expr = match (List.nth form.sigma i1) with
			| Hpointsto (a,_,b) -> (find_vars_expr a),(expr_to_solver_only_exp ctx z3_names a),b,a
			| _ -> [],(Boolean.mk_false ctx),Exp.Undef,Exp.Undef
	in
	(* The parameter p2 should be modified by offset if the linking field is not in the beginning of the data structure.
	   The offset is computed as a difference p1_dest-p2 *)
	let p2,p2_lambda = match (List.nth form.sigma i2) with
			| Hpointsto (b,_,a) -> 
				if a=Const(Ptr 0) then [a],(find_vars_expr b)
				else
				(
				let offset=try_simplify_SL_expr_to_int {ctx=ctx; solv=solv; z3_names=z3_names} form (Exp.BinOp (Pminus,b,p1_dest_expr)) in
				match offset with
				| None -> [],[]
				| Some 0L -> [a],(find_vars_expr b)
				| Some i -> [Exp.BinOp (Pplus,a,Const (Int i))],(find_vars_expr b)
				)
			| _ -> [],[]
	in
	let r2,r2_dest,r2_dest_expr = if y2<0 then [],[],Exp.Undef
		else 
		match (List.nth form.sigma y2) with
			| Hpointsto (a,_,b) -> (find_vars_expr a),(find_vars_expr b),b
			| _ -> [],[],Exp.Undef
	in
	let r1,r1_lambda,r1_z3 = if y1<0 then [],[], (Boolean.mk_false ctx)
		else
		match  (List.nth form.sigma y1) with
		| Hpointsto (b,_,a) ->
			(
			let offset=try_simplify_SL_expr_to_int {ctx=ctx; solv=solv; z3_names=z3_names} form (Exp.BinOp (Pminus,p1_expr,r2_dest_expr)) in
			match offset,dll_backlink with
			| None, _ -> [],[],(Boolean.mk_false ctx)
			| Some 0L,-1 -> [a], (find_vars_expr a),(expr_to_solver_only_exp ctx z3_names b)
			| Some i, -1 -> [Exp.BinOp (Pplus,a,Const (Int i))],(find_vars_expr a),(expr_to_solver_only_exp ctx z3_names b)
			| Some 0L, back_l -> [a],[back_l] ,(expr_to_solver_only_exp ctx z3_names b)
			| Some i, back_l -> [Exp.BinOp (Pplus,a,Const (Int i))],[back_l],(expr_to_solver_only_exp ctx z3_names b)
			)

		| _ -> [],[], (Boolean.mk_false ctx)
	in
	(* check direction of the dll folding *)
	let dll_dir=if y1<0 
		then 1
		else 
		let query= [ BitVector.mk_slt ctx p1_z3 r1_z3 ] in
		if (Solver.check solv query)=SATISFIABLE then 1 else 2
	in
	(* in the case of DLL (y1!=-1), r2_dest=p1 must be valid. Othervice we can not easily establish a lambda with 3 parameters only.*)
	match p1,p2,p2_lambda,r1,r2,r1_lambda,y1,(p1=r2_dest),dll_dir with (* we want only a single variable on the LHS of a pointsto *)
	| [a],[d],[d_lambda],_,_,_,-1,_,1 -> 
		let lambda={param=[a;d_lambda] @ shared_vars; 
			form=(simplify_lambda  {pi=form.pi; sigma=(new_lambda)} (List.filter (nomem [a;d_lambda]) (find_vars form)) [d_lambda])
		} in
		AbstractionApply {pi=form.pi; sigma=(get_new_sigma 0) @ [Slseg (Exp.Var a, d, (lambda_close lambda),shared_exprs)]}
	| [a],[d],[d_lambda],[b],[c],[b_lambda],_,true,1 ->  (* forward folding *)
		let lambda={param=[a;d_lambda;b_lambda]; 
			form=(simplify_lambda  {pi=form.pi; sigma=(new_lambda)} 
						(List.filter (nomem [a;d_lambda;b_lambda]) (find_vars form)) 
						[d_lambda;b_lambda])
		} in
		AbstractionApply {pi=form.pi; sigma=(get_new_sigma 0) @ [Dlseg (Exp.Var a, b, Exp.Var c, d, (lambda_close lambda))]}
	| [a],[d],[d_lambda],[b],[c],[b_lambda],_,true,2 ->  (* backward folding *)
		let lambda={param=[a;b_lambda;d_lambda]; 
			form=(simplify_lambda  {pi=form.pi; sigma=(new_lambda)} 
					(List.filter (nomem [a;d_lambda;b_lambda]) (find_vars form))
					[d_lambda;b_lambda])
		} in
		AbstractionApply {pi=form.pi; sigma=(get_new_sigma 0) @ [Dlseg (Exp.Var c, d, Exp.Var a, b, (lambda_close lambda))]}
	| _ -> AbstractionFail


(* check that the pointsto (and its neighbourhood) is compatible with lambda in the slseg 
  it works as follows: 
  1) the slseg is unfolded
  2) the match_pointsto_from_two_blocks and check_matched_pointsto ctx solv are used to check whether the pointsto is compatible with lambda 
  3) lambda may be updated

  flag: 0: pointsto(x,y) * slseg(y,z) [ pointsto(x,y) * Dlseg(y,z) ]
        1: slseg(x,y) * pointsto(y,z)
	2:  Dlseg(x,y) * pointsto(y,z)
*)
let try_add_lseg_to_pointsto form i_pto i_slseg gvars flag=
	let unfolded_form,_=
		if flag=2 
		then  unfold_predicate form i_slseg gvars 2 (* unfold dLL from the end *)
		else unfold_predicate form i_slseg gvars 1 in
	let i_unfolded_slseg=(List.length unfolded_form.sigma)-1 in (* index of the partially unfolded slseg *)
	let new_i1=if i_pto<i_slseg then i_pto else (i_pto-1) in
	(* create a fresh solver --  the main one contains asserted "form" but we need to assert unfolded form *)
	let solver2=Z3wrapper.config_solver () in
	let ctx=solver2.ctx in
	let solv=solver2.solv in
	let z3_names=solver2.z3_names in
	Solver.add solv (formula_to_solver ctx unfolded_form);	
	(* serch for the index i2 in the unfolded_form,
	   i2 is within the unfolded part of the formula, which 
	   starts at index="(List.length form.sigma)-1"*)
	let rec find_new_i2 a1 l1 b1 index =
		if index=(List.length unfolded_form.sigma) then -1
		else
		match (List.nth unfolded_form.sigma index) with
		| Hpointsto (aa,ll,bb) ->
			let a2,l2,b2= (expr_to_solver_only_exp ctx z3_names aa),
					(expr_to_solver_only_exp ctx z3_names ll),
					(expr_to_solver_only_exp ctx z3_names bb)  in
			(* First do a base check --- i.e. query1 + query2 *)
			(* flag=0: form -> base(a1) != base(a2) /\ l1 = l2 /\ base(b1) = base(a2) *)
			(* flag=1: form -> base(a1) != base(a2) /\ l1 = l2 /\ base(endlist) = base(a1) *)
			(* flag=2: form -> base(a1) != base(a2) /\ l1 = l2 /\ base(b2) = base(a1) *)
			let endlist = (* get the expression at the end of the unfolded list *)
				match (List.nth unfolded_form.sigma  i_unfolded_slseg) with
				| Slseg (_,b,_,_) -> (expr_to_solver_only_exp ctx z3_names b)
				| Dlseg (_,_,_,b,_) -> (expr_to_solver_only_exp ctx z3_names b) 
				| _ -> raise_notrace (ErrorInAbstraction ("Incompatible unfolding",__POS__))
			in	
			let e1,e2=
				match flag with 
				| 0 -> b1,a2 
				| 1 -> endlist,a1
				| 2 -> b2,a1
				| _ -> raise_notrace (ErrorInAbstraction ("Incorrect flag",__POS__))
			in
			let query1 = [	
				Boolean.mk_or ctx [
					(Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [a1]) (Expr.mk_app ctx z3_names.base [a2]));
					(Boolean.mk_not ctx (Boolean.mk_eq ctx l1 l2));
					(Boolean.mk_not ctx (Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [e1]) (Expr.mk_app ctx z3_names.base [e2])))]
			] in
			(* SAT: form /\ a1-base(a1) = a2 - base(a2) *)
			let query2 = [ 
				Boolean.mk_eq ctx 
					(BitVector.mk_sub ctx  a1 (Expr.mk_app ctx z3_names.base [a1]) )
					(BitVector.mk_sub ctx  a2 (Expr.mk_app ctx z3_names.base [a2]) )
			] in
			if not (((Solver.check solv query1)=UNSATISFIABLE)
			&& ((Solver.check solv query2)=SATISFIABLE)) then (find_new_i2 a1 l1 b1 (index+1))
			else (
				(* add query2 into the solver to enable handling linux-list style data structures, where base adresses
				   are not fixed.
				   The solver is discarted at the end of this function -> no need to do Solver.push/pop commands *)
				Solver.add solv query2;
				index
			)

		| _ -> find_new_i2 a1 l1 b1 (index+1)
	in
	(* sanity check that the unfolding works ok *)
	if not ((List.nth form.sigma i_pto)=(List.nth unfolded_form.sigma new_i1)) 
	then raise_notrace (ErrorInAbstraction ("This should not happen - Problem with unfolding",__POS__)) (*AbstractionFail*)
	else
	match (List.nth unfolded_form.sigma new_i1) with
	| Hpointsto (a,l,b) -> (
		let a1,l1,b1= (expr_to_solver_only_exp ctx z3_names a), 
				(expr_to_solver_only_exp ctx z3_names l),
				(expr_to_solver_only_exp ctx z3_names b) in
		let new_i2=find_new_i2 a1 l1 b1 ((List.length form.sigma)-1) in (* try to find i2 in the unfolded part of the formula *)
		if (new_i2=(-1)) then AbstractionFail
		else
		(* swap new_i1 and new_i2 and a1 and a2 in the case of flag=1/2 --- folding on the end of the list *)
		let a2= match (List.nth unfolded_form.sigma new_i2) with
			| Hpointsto (aa,_,_) -> (expr_to_solver_only_exp ctx z3_names aa) 
			| _ -> raise_notrace (ErrorInAbstraction ("This should not happen",__POS__))
		in
		let new_i1,new_i2,a1,a2=
			match flag with
			| 1 | 2 -> new_i2,new_i1,a2,a1			
			| _ -> new_i1,new_i2,a1,a2
		in
		let a1_block=get_eq_base ctx solv z3_names unfolded_form a1 0 0 [new_i1;new_i2] 0 in
		let a2_block=get_eq_base ctx solv z3_names unfolded_form a2 0 0 ([new_i1;new_i2]@a1_block) 0 in
		(* FIRST: try to find possible mapping between particular points-to predicates is block of a1/a2 *)
		match match_pointsto_from_two_blocks ctx solv z3_names unfolded_form a1_block a2_block with
		| MatchFail ->  AbstractionFail
		| MatchOK matchres ->
			match (check_matched_pointsto ctx solv z3_names unfolded_form matchres [(a1,a2,1)] 1 gvars) with
			| CheckOK checked_matchres -> 
				fold_pointsto_slseg {ctx=ctx; solv=solv; z3_names=z3_names} form i_slseg unfolded_form new_i1 new_i2 checked_matchres flag
			| CheckFail ->  AbstractionFail
			| DlsegBackLink -> raise_notrace (ErrorInAbstraction ("DllBackLink is not expected here",__POS__))
	)
	| _ -> AbstractionFail

(* try to abstract two predicates i1 and i2 into a list segment,
  pvars = program variables (global vars + vars of function), they must not be abstracted.
      Internal nodes of the list segment can not be pointed by global variables*)
let try_abstraction_to_lseg_ll {ctx=ctx; solv=solv; z3_names=z3_names} form i1 i2 pvars =
  	(* SAT: forall g in gvar. base(g)!=base(middle) *)
	let global_bases middle g=Boolean.mk_not ctx
			(Boolean.mk_eq ctx
				(Expr.mk_app ctx z3_names.base [middle]) 
				(Expr.mk_app ctx z3_names.base [(expr_to_solver_only_exp ctx z3_names (Exp.Var g))])
			)
	in
	let query_pvars middle=if pvars=[] then []
		else
		[ 
			Boolean.mk_and ctx (List.map (global_bases middle) pvars) ] 
	in
	(* auxiliary function for list-list cases *)
	let rec remove_i1_i2 ll index=
		if index=List.length ll then []
		else if (index=i1) || (index=i2) then remove_i1_i2 ll (index+1)
		else (List.nth ll index) :: remove_i1_i2 ll (index+1) 
	in
	let check_list_pto_conditions b aa= 
		let b1= (expr_to_solver_only_exp ctx z3_names b) in
		let a2= (expr_to_solver_only_exp ctx z3_names aa) in
		(* form -> base(b1) = base(a2) *)
		let query1 = [	
				(Boolean.mk_not ctx (Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [b1]) (Expr.mk_app ctx z3_names.base [a2])))
		] in		
		(((Solver.check solv query1)=SATISFIABLE)  || (((Solver.check solv (query_pvars a2))=UNSATISFIABLE)))
	in
				
	match (List.nth form.sigma i1), (List.nth form.sigma i2) with
	| Hpointsto (a,l,b), Hpointsto (aa,ll,bb) -> ( 
		let a1,l1,b1= (expr_to_solver_only_exp ctx z3_names a),
				(expr_to_solver_only_exp ctx z3_names l),
				(expr_to_solver_only_exp ctx z3_names b) in
		let a2,l2,_= (expr_to_solver_only_exp ctx z3_names aa),
				(expr_to_solver_only_exp ctx z3_names ll),
				(expr_to_solver_only_exp ctx z3_names bb) in
		(* First do a base check --- i.e. query1 + query2 *)
		(* form -> l1 = l2 /\ base(b1) = base(a2) *)
		let query1A = [	(Boolean.mk_not ctx (Boolean.mk_eq ctx l1 l2))] in
		let query1B = [ (Boolean.mk_not ctx (Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [b1]) (Expr.mk_app ctx z3_names.base [a2])))] in
		(* offset check: SAT: form /\  base(a1) != base(a2) /\ a1-base(a1) = a2 - base(a2) *)
		let query2 = [ 
			Boolean.mk_not ctx (Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [a1]) (Expr.mk_app ctx z3_names.base [a2]));
			Boolean.mk_eq ctx 
				(BitVector.mk_sub ctx a1 (Expr.mk_app ctx z3_names.base [a1]) )
				(BitVector.mk_sub ctx a2 (Expr.mk_app ctx z3_names.base [a2]) )
		] in
		(* check queries lazily one-by-one *)
		let rec checkqueries q =
			match q with
			| [] -> true
			| (query,res)::rest -> 
				if (Solver.check solv query)=res
				then checkqueries rest
				else false
		in
		if not (checkqueries [(query1A, UNSATISFIABLE);
					(query1B,UNSATISFIABLE);
					(query2,SATISFIABLE); 
					(query_pvars a2, SATISFIABLE)])
		then  AbstractionFail
		else 
		(
		(* ADD: base(a1) != base(a2) /\ a1-base(a1) = a2 - base(a2) to the solver for the following computations 
		   this is needed for linux-list like examples, where the bases are only relative---i.e. we do not know the 
		   exact distance from the base
		   The added constrains are poped from the solver in the function  try_abstraction_to_lseg *)
		Solver.add solv query2;
		(* check all pointsto with equal bases to a1/a2 *)
		(* get all indices i in form.sigma s.t. 'List.nth form.sigma i' is a points-to 
		predicate with the same base address as a1 resp. a2 = every points-to which is in the same
		block as a1 resp. a2*)
		(* find everything which is in the same block as a1*)
		let a1_block=get_eq_base ctx solv z3_names form a1 0 0 [i1;i2] 0 in 
		(* ... @a1_block is for performance and could be omitted*)
		let a2_block=get_eq_base ctx solv z3_names form a2 0 0 ([i1;i2]@a1_block) 0 in 
		(* FIRST: try to find possible mapping between particula points-to predicates is block of a1/a2 *)
		match match_pointsto_from_two_blocks ctx solv z3_names form a1_block a2_block with
		| MatchFail ->  AbstractionFail 
		| MatchOK matchres -> (* SECOND: check that the mapped pointsto behave in an equal way *)
		(* a1, a2 are the points-to predicates linking the nodes*)
			match (check_matched_pointsto ctx solv z3_names form matchres [(a1,a2,1)] 1 pvars) with
			| CheckOK checked_matchres ->  
				(fold_pointsto ctx solv z3_names form i1 i2 checked_matchres) 
				
			| CheckFail ->  AbstractionFail
			| DlsegBackLink -> raise_notrace (ErrorInAbstraction ("DllBackLink is not expected here",__POS__))
		)
		)
	| Slseg(a,b,l1, shared1), Slseg(aa,bb,l2,_) -> (
		let b1= (expr_to_solver_only_exp ctx z3_names b) in
		let a2= (expr_to_solver_only_exp ctx z3_names aa) in
		(* form -> b1 = a2 *)
		let query1 = [	
				(Boolean.mk_not ctx (Boolean.mk_eq ctx b1 a2))
		] in
		if (Solver.check solv query1)=SATISFIABLE 
			|| ((Solver.check solv (query_pvars a2))=UNSATISFIABLE) then AbstractionFail
		else
			
		(* we use a fresh solver, because the current one is used in incremental way for solving the Abstraction queries *)
		(* TODO: 'shared1' is just a placeholder, need to implement shared nodes handling here*)
		(match (Abduction.check_lambda_entailment (config_solver ()) l1 l2) 0 with
			| 1 -> AbstractionApply {pi=form.pi; sigma=Slseg(a,bb,l2,shared1) :: (remove_i1_i2 form.sigma 0)}
			| 2 -> AbstractionApply {pi=form.pi; sigma=Slseg(a,bb,l1,shared1) :: (remove_i1_i2 form.sigma 0)}
			| _ -> AbstractionFail
		)
	)
	| Dlseg(a,b,c,d,l1), Dlseg(aa,bb,cc,dd,l2) -> (
		let d1= (expr_to_solver_only_exp ctx z3_names d) in
		let c1= (expr_to_solver_only_exp ctx z3_names c) in
		let a2= (expr_to_solver_only_exp ctx z3_names aa) in
		let b2= (expr_to_solver_only_exp ctx z3_names bb) in
		(* form -> d1 = a2 /\ b2=c1 *)
		let query1 = [	
				(Boolean.mk_not ctx 
				(Boolean.mk_and ctx [(Boolean.mk_eq ctx d1 a2);(Boolean.mk_eq ctx b2 c1); ])
				)
		] in
		if (Solver.check solv query1)=SATISFIABLE 
			|| ((Solver.check solv ((query_pvars a2)@(query_pvars c1)))=UNSATISFIABLE) then AbstractionFail
		else
			
		(* we use a fresh solver, because the current one is used in incremental way for solving the Abstraction queries *)
		(match (Abduction.check_lambda_entailment (config_solver ()) l1 l2) 0 with
			| 1 -> AbstractionApply {pi=form.pi; sigma=Dlseg(a,b,cc,dd,l2) :: (remove_i1_i2 form.sigma 0)}
			| 2 -> AbstractionApply {pi=form.pi; sigma=Dlseg(a,b,cc,dd,l1) :: (remove_i1_i2 form.sigma 0)}
			| _ -> AbstractionFail
		)
	)
	| Hpointsto (_,_,b), Slseg (aa,_,_,_) 
	| Hpointsto (_,_,b), Dlseg (aa,_,_,_,_) -> (
		if check_list_pto_conditions b aa then AbstractionFail
		else
			(* the process continues as follows: Slseg on is unfolded and then similar process as folding of Hpointsto x Hpointsto is appplied *)
			try_add_lseg_to_pointsto form i1 i2 pvars 0

	)
	|  Slseg (_,b,_,_),Hpointsto (aa,_,_) -> (
		if check_list_pto_conditions b aa then AbstractionFail 
		else
			(* the process continues as follows: Slseg on is unfolded and then similar process as folding of Hpointsto x Hpointsto is appplied *)
			try_add_lseg_to_pointsto form i2 i1 pvars 1

	)
	|  Dlseg (_,_,_,b,_),Hpointsto (aa,_,_) -> (
		if check_list_pto_conditions b aa then AbstractionFail 
		else
			(* the process continues as follows: Slseg on is unfolded and then similar process as folding of Hpointsto x Hpointsto is appplied *)
			try_add_lseg_to_pointsto form i2 i1 pvars 2

	)
	| _ -> AbstractionFail 

let try_abstraction_to_lseg solver form i1 i2 pvars =
	(* in the try_abstraction_to_lseg_ll, we add some contraints related to bases of i1 i2 
	   --> we need to remove them from the solver at the end of the function *)
	Solver.push solver.solv;
	let res=try_abstraction_to_lseg_ll solver form i1 i2 pvars in
	Solver.pop solver.solv 1;
	res

(* try list abstraction - first tries the last added, at least 2 predicates in
	sigma *)
(* TOP level function of abstraction iterating through all pairs of points-to/ls predicates  *)
let rec lseg_abstraction_ll solver form pvars =
	let rec f i j =
		(*Printf.printf "%d,%d\n" i j; *)
		let result = 
			try try_abstraction_to_lseg solver form i j pvars 
			with Get_eq_base_TO -> AbstractionFail
		in
		match result with
		| AbstractionApply new_form ->
			lseg_abstraction_ll solver new_form pvars
		| AbstractionFail -> (
			let result_rev = 
				try try_abstraction_to_lseg solver form j i pvars 
				with Get_eq_base_TO -> AbstractionFail
			in
			match result_rev with
			| AbstractionApply new_form ->
				lseg_abstraction_ll solver new_form pvars
			| AbstractionFail -> (
				match i,j with
				| 1,_ -> form (* nothing change *)
				| _,0 -> f (i-1) (i-2)
				| _,_ -> f i (j-1)
			)
		)
	in
	let n = List.length form.sigma in
	(* assert (n>1); *)
	if (n<2) then form else f (n-1) (n-2) 

let lseg_abstraction _ form pvars=
	(* form is a common part of all SMT queries. Add it now to improve efficiency. *)
	let solver=config_solver_to (Config.solver_timeout_abstraction ()) in
	Solver.add solver.solv (formula_to_solver solver.ctx form);
	let res=lseg_abstraction_ll solver form pvars in
	Solver.reset solver.solv; 
	res

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

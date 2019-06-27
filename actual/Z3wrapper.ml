(* in Utop use 
	#load "Formula.cmo" or #mod_use "Formula.ml" 
   	#require "z3" 
*)

open Z3
open Z3.Symbol
open Z3.Arithmetic

open Formula

(* The functions base, len, size, etc in SL are used as uninterpreted functions in z3 *)
type sl_function_names_z3 = {
	base : FuncDecl.func_decl;
	len : FuncDecl.func_decl;
	alloc : FuncDecl.func_decl;
	}

let get_sl_functions_z3 ctx =
	{
	  base=FuncDecl.mk_func_decl ctx (Symbol.mk_string ctx "base") [(Integer.mk_sort ctx)] (Integer.mk_sort ctx);
	  len=FuncDecl.mk_func_decl ctx (Symbol.mk_string ctx "len") [(Integer.mk_sort ctx)] (Integer.mk_sort ctx);
	  alloc=FuncDecl.mk_func_decl ctx (Symbol.mk_string ctx "alloc") [(Integer.mk_sort ctx)] (Boolean.mk_sort ctx);
	}



(* Pure part translation into Z3 solver internam representation *)

let const_to_solver ctx c=
	match c with
	| Exp.Ptr a -> Integer.mk_numeral_i ctx a
	| Exp.Int a -> Integer.mk_numeral_i ctx a
	| Exp.Bool a -> Boolean.mk_val ctx a
	(*| Exp.String a -> a *)
	(* | Exp.Float a -> Real.mk_numeral_i ctx a *)





let rec expr_to_solver ctx func expr =
	match expr with
	    | Exp.Var a -> Expr.mk_const ctx (Symbol.mk_string ctx (string_of_int a)) (Integer.mk_sort ctx)
	    | Exp.Const a -> const_to_solver ctx a
	    | Exp.UnOp (op,a) -> 
	    	( match op with 
			| Base -> Expr.mk_app ctx func.base [(expr_to_solver ctx func a)]
			| Len ->  Expr.mk_app ctx func.len [(expr_to_solver ctx func a)]
			| Freed -> Boolean.mk_not ctx (Expr.mk_app ctx func.alloc [(expr_to_solver ctx func a)])
		)
	    | Exp.BinOp (op,a,b) -> 
	    	(match op with 
		| Peq ->  Boolean.mk_eq ctx (expr_to_solver ctx func a) (expr_to_solver ctx func b)
		| Pneq -> Boolean.mk_not ctx (Boolean.mk_eq ctx (expr_to_solver ctx func a) (expr_to_solver ctx func b))
		| Pless ->  Arithmetic.mk_lt ctx (expr_to_solver ctx func a) (expr_to_solver ctx func b)
		| Plesseq -> Arithmetic.mk_le ctx (expr_to_solver ctx func a) (expr_to_solver ctx func b)
	      	| Pplus -> Arithmetic.mk_add ctx [ (expr_to_solver ctx func a); (expr_to_solver ctx func b) ]
      		| Pminus -> Arithmetic.mk_sub ctx [ (expr_to_solver ctx func a); (expr_to_solver ctx func b) ]
		)
	    | Exp.Void ->  Integer.mk_numeral_i ctx (-1)
	    | Exp.Undef -> Expr.mk_fresh_const ctx "UNDEF" (Integer.mk_sort ctx)
	    (**| Exp.Undef -> Integer.mk_numeral_i ctx (-2) !!! This may be a problem. We may create a fresh variable for this .... *)


(* create conditions to guarantee SL * validity ... *)
(*	" a-> ... => alloc(base a)  " *)
(*	" x-> ... * y -> ... => x!=y "/\" [base(x)= base(y) => y + size_y<=x "\/" x+size_x<=y] " *)

let rec spatial_pred_to_solver ctx sp_pred1 rest_preds func =
	let alloc x=(expr_to_solver ctx func x) in
	let base_eq x y =
		Boolean.mk_eq ctx 
		  (Expr.mk_app ctx func.base [x])
		  (Expr.mk_app ctx func.base [y])
	in
	match sp_pred1 with
	| Hpointsto (a, size, _) -> (		
		(* Create "local" constraints for a single points-to *)
		(* local_c[123] = alloc(base a) 
				/\ len(x) >=size*)
		let x=alloc a in
		let local_c1= Expr.mk_app ctx func.alloc [Expr.mk_app ctx func.base [x]] in
		let local_c3 = Arithmetic.mk_ge ctx
			(Expr.mk_app ctx func.len [x])
			(Integer.mk_numeral_i ctx size)
		in
		(* Create constrains for two space predicates *)
		(*  dist_fields: x!=y /\ [base(x)= base(y) => y + size_y<=x \/ x+size_x<=y] *)
		let no_overlap x size_x y size_y= 
			Boolean.mk_or ctx 
			[(Arithmetic.mk_le ctx (Arithmetic.mk_add ctx [x; (Integer.mk_numeral_i ctx size_x) ]) y);
			(Arithmetic.mk_le ctx (Arithmetic.mk_add ctx [y; (Integer.mk_numeral_i ctx size_y) ]) x)]
		in
		let dist_fields x size_x y size_y = Boolean.mk_implies ctx (base_eq x y) (no_overlap x size_x y size_y) in				
		let two_sp_preds_c al sp_rule = 
			match sp_rule with 
			| Hpointsto (aa, size_aa, _) ->(* create a nonequality al != x, where x is the allocated node in sp_rule *)
				Boolean.mk_and ctx 
				[(Boolean.mk_not ctx (Boolean.mk_eq ctx al (alloc aa)));
				(dist_fields al size (alloc aa) size_aa)]
			| Slseg (aa,bb,_) -> (* base(al) != base(aa) or Slseq is empty aa=bb *)
				Boolean.mk_or ctx 
				[ Boolean.mk_not ctx (base_eq al (alloc aa));
				Boolean.mk_eq ctx (alloc aa) (alloc bb) ]
		in
		let rec create_noneq to_parse =
			match to_parse with
			| first:: rest -> (two_sp_preds_c x first) :: create_noneq rest
			| [] -> []
		in
		(Boolean.mk_and ctx [ local_c1; local_c3]) :: create_noneq rest_preds
		)
	| Slseg (a,b,_) -> 
		let x=alloc a in
		let y=alloc b in
		(* alloc base(x) or x=y *)
		let c1 = Boolean.mk_or ctx 
			[ Expr.mk_app ctx func.alloc [Expr.mk_app ctx func.base [x]];
			Boolean.mk_eq ctx x y]	in
		let two_sp_preds_c al dst sp_rule = 
			match sp_rule with 
			| Hpointsto (aa, _, _) -> (* base(al) != base(aa) or Slseq is empty al=dst *)
				Boolean.mk_or ctx 
				[ Boolean.mk_not ctx (base_eq al (alloc aa) );
				Boolean.mk_eq ctx al dst ]
			| Slseg (aa,bb,_) ->(* base(al) != base(aa) or one of the Slseqs is empty al=dst \/ aa=bb *) 
				Boolean.mk_or ctx 
				[ Boolean.mk_not ctx (base_eq al (alloc aa) );
				Boolean.mk_eq ctx al dst;
				Boolean.mk_eq ctx (alloc aa) (alloc bb) ]
				
		in
		let rec sp_constraints to_parse =
			match to_parse with
				| first:: rest -> (two_sp_preds_c x y first) :: sp_constraints rest
				| [] -> []
		in
		c1:: (sp_constraints rest_preds)

(* Creation of the Z3 formulae for a SL formulae *)

let rec pi_to_solver ctx names_z3 pi =
	match pi with 
	| [] -> []
	| first::rest -> (expr_to_solver ctx names_z3 first) :: (pi_to_solver ctx names_z3 rest)

let rec sigma_to_solver ctx names_z3 sigma =
	match sigma with
	| [] -> []
	| first::rest -> List.append (spatial_pred_to_solver ctx first rest names_z3) (sigma_to_solver ctx names_z3 rest)

let formula_to_solver ctx form =
	let names_z3=get_sl_functions_z3 ctx in
	let pi= pi_to_solver ctx names_z3 form.pi in
	let sigma= sigma_to_solver ctx names_z3 form.sigma in
	List.append pi (List.append sigma [])
	(*List.append pi (List.append sigma global_constr)*)


(* check the lambda within the Slseq predicates,
   returns **true** iff the lambda satisfy the basic properties *)
let rec check_sp_predicate ctx solv pred =
	let z3_names=get_sl_functions_z3 ctx in
	match pred with
	| Slseg(_,_,lambda) ->
		(* basic checks, there must be two parameters, which are different *)
		if not ((List.length lambda.param) = 2) || 
			(List.nth lambda.param 0) = (List.nth lambda.param 1) then false
		else 
			let lambda_z3=formula_to_solver ctx lambda.form in
			let x=expr_to_solver ctx z3_names (Exp.Var (List.nth lambda.param 0)) in
			let y=expr_to_solver ctx z3_names (Exp.Var (List.nth lambda.param 1)) in
			let not_alloc_base_x = Boolean.mk_not ctx
				(Expr.mk_app ctx z3_names.alloc [Expr.mk_app ctx z3_names.base [x]]) in
			let not_alloc_base_y = Boolean.mk_not ctx
				(Expr.mk_app ctx z3_names.alloc [Expr.mk_app ctx z3_names.base [y]]) in
			(* Check that 1: labda /\ not(alloc(y) is SAT and 2: lambda => alloc(x) *)
			(Solver.check solv (not_alloc_base_y::lambda_z3))=SATISFIABLE &&
			(Solver.check solv (not_alloc_base_x::lambda_z3))=UNSATISFIABLE &&
			(check_all_lambdas ctx solv lambda.form.sigma)
	| _ -> true

and check_all_lambdas ctx solv sigma =
	match sigma with
	| [] -> true
	| first::rest -> (check_sp_predicate ctx solv first) && (check_all_lambdas ctx solv rest)


(* Experiments *)

(*
let cfg = [("model", "true"); ("proof", "false")]
let ctx = (mk_context cfg)

open Solver
let z3_form1=formula_to_solver ctx form1

let solv = (mk_solver ctx None)
check solv z3_form1

------------------------------------
let form5=
	let lambda= {param=[1;2] ;form={
	    sigma = [ Hpointsto (Var 1, 8, Var 2); Hpointsto (Var 2, 8, Var 3) ]; pi=[] }}
	in
	{
    	    sigma = [ Hpointsto (Var 1,8, Var 2); Slseg (Var 3, Var 4, lambda) ];
	    pi = [ BinOp ( Peq, Var 1, UnOp ( Base, Var 1));
    		  BinOp ( Peq, Var 1, UnOp ( Base, Var 3));
	          BinOp ( Peq, UnOp ( Len, Var 1), Const (Int 8));
	          BinOp ( Peq, Var 1, Var 2332 );
	          BinOp ( Peq, Var 2, Const (Ptr 0)) ]
	}

check_all_lambdas ctx solv form4.sigma;;
check_all_lambdas ctx solv form5.sigma;;

*)

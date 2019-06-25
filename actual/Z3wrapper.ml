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

(* Global restrictions for base/len/size functions *)

let create_global_restrictions ctx names_z3 =
	(* forall x: (x - base(x)) + len(x) = len( base(x)) *)
	let x=Quantifier.mk_bound ctx 0 (Integer.mk_sort ctx) in
	let l=Arithmetic.mk_add ctx [ (Arithmetic.mk_sub ctx [x;(Expr.mk_app ctx names_z3.base [x] )]); (Expr.mk_app ctx names_z3.len [x]) ] in
	let r=Expr.mk_app ctx names_z3.len [ (Expr.mk_app ctx names_z3.base [x]) ] in
	let eq = Boolean.mk_eq ctx l r in
	let q=Quantifier.mk_exists ctx [(Integer.mk_sort ctx)] [ (Symbol.mk_string ctx "x")] eq 
		(Some 1) [] [] (Some (Symbol.mk_string ctx "Q1")) (Some (Symbol.mk_string ctx "skid1")) in
	[ Quantifier.expr_of_quantifier q]

(* create conditions to guarantee SL * validity ... *)
(*	" a-> ... => alloc(base a)  " *)
(*	" x-> ... * y -> ... => x!=y "/\" [base(x)= base(y) => y + size_y<=x "\/" x+size_x<=y] " *)

let rec spatial_pred_to_solver ctx sp_pred1 rest_preds func =
	let alloc x=(expr_to_solver ctx func x) in
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
		(* Create constrains for two points-to *)
		(*  x!=y /\ [base(x)= base(y) => y + size_y<=x \/ x+size_x<=y] *)
		let dist_l x y =
			Boolean.mk_eq ctx 
			  (Expr.mk_app ctx func.base [x])
			  (Expr.mk_app ctx func.base [y])
		in
		let dist_r x size_x y size_y= 
			Boolean.mk_or ctx 
			[(Arithmetic.mk_le ctx (Arithmetic.mk_add ctx [x; (Integer.mk_numeral_i ctx size_x) ]) y);
			(Arithmetic.mk_le ctx (Arithmetic.mk_add ctx [y; (Integer.mk_numeral_i ctx size_y) ]) x)]
		in
		let dist_fields x size_x y size_y = Boolean.mk_implies ctx (dist_l x y) (dist_r x size_x y size_y) in				
		let two_vars_c al sp_rule = (* create a nonequality al != x, where x is the allocated nod in sp_rule *)
			match sp_rule with 
			| Hpointsto (aa, size_aa, _) ->
				Boolean.mk_and ctx 
				[(Boolean.mk_not ctx (Boolean.mk_eq ctx al (alloc aa)));
				(dist_fields al size (alloc aa) size_aa)]
			| Slseg (aa,bb,_) -> 
				Boolean.mk_or ctx 
				[ Boolean.mk_not ctx (Boolean.mk_eq ctx 
							( Expr.mk_app ctx func.base [al]) 
							( Expr.mk_app ctx func.base [(alloc aa)] ));
				Boolean.mk_eq ctx (alloc aa) (alloc bb) ]
		in
		let rec create_noneq to_parse =
			match to_parse with
			| first:: rest -> (two_vars_c (alloc a) first) :: create_noneq rest
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
			| Hpointsto (aa, _, _) ->
				Boolean.mk_or ctx 
				[ Boolean.mk_not ctx (Boolean.mk_eq ctx 
							( Expr.mk_app ctx func.base [al]) 
							( Expr.mk_app ctx func.base [(alloc aa)] ));
				Boolean.mk_eq ctx al dst ]
			| Slseg (aa,bb,_) -> 
				Boolean.mk_or ctx 
				[ Boolean.mk_not ctx (Boolean.mk_eq ctx 
							( Expr.mk_app ctx func.base [al]) 
							( Expr.mk_app ctx func.base [(alloc aa)] ));
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

(* Experiments *)

(*
let cfg = [("model", "true"); ("proof", "false")]
let ctx = (mk_context cfg)

open Solver
let z3_form1=formula_to_solver ctx form1

let solv = (mk_solver ctx None)
check solv z3_form1
*)

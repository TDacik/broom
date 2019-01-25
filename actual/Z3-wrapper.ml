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
	size : FuncDecl.func_decl;
	base : FuncDecl.func_decl;
	len : FuncDecl.func_decl;
	freed : FuncDecl.func_decl;
	field : FuncDecl.func_decl;
	}

let get_sl_functions_z3 ctx =
	{
	  size=FuncDecl.mk_func_decl ctx (Symbol.mk_string ctx "size") [(Integer.mk_sort ctx)] (Integer.mk_sort ctx);
	  base=FuncDecl.mk_func_decl ctx (Symbol.mk_string ctx "base") [(Integer.mk_sort ctx)] (Integer.mk_sort ctx);
	  len=FuncDecl.mk_func_decl ctx (Symbol.mk_string ctx "len") [(Integer.mk_sort ctx)] (Integer.mk_sort ctx);
	  freed=FuncDecl.mk_func_decl ctx (Symbol.mk_string ctx "freed") [(Integer.mk_sort ctx)] (Boolean.mk_sort ctx);
	  field=FuncDecl.mk_func_decl ctx (Symbol.mk_string ctx "field") [(Integer.mk_sort ctx)] (Boolean.mk_sort ctx);
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
			| Size -> Expr.mk_app ctx func.size [(expr_to_solver ctx func a)]
			| Freed -> Expr.mk_app ctx func.freed [(expr_to_solver ctx func a)]
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
	    | Exp.Undef -> Integer.mk_numeral_i ctx (-2)

(* Global restrictions for base/len/size functions *)

let create_global_restrictions ctx names_z3 =
	(* forall x: (x - base(x)) + len(x) = len( base(x)) *)
	let x=Quantifier.mk_bound ctx 0 (Integer.mk_sort ctx) in
	let l=Arithmetic.mk_add ctx [ (Arithmetic.mk_sub ctx [x;(Expr.mk_app ctx names_z3.base [x] )]); (Expr.mk_app ctx names_z3.len [x]) ] in
	let r=Expr.mk_app ctx names_z3.len [ (Expr.mk_app ctx names_z3.base [x]) ] in
	let eq = Boolean.mk_eq ctx l r in
	let q=Quantifier.mk_exist ctx [(Integer.mk_sort ctx)] [ (Symbol.mk_string ctx "x")] eq 
		(Some 1) [] [] (Some (Symbol.mk_string ctx "Q1")) (Some (Symbol.mk_string ctx "skid1")) in
	[ Quantifier.expr_of_quantifier q]

(* create conditions to guarantee SL * validity ... "x-> ... * y -> ..." => x !=y *)

let rec spatial_pred_to_solver ctx sp_pred1 rest_preds func =
	let alloc x=(expr_to_solver ctx func x) in
	let noneq_rule al sp_rule = (* create a nonequality al != x, where x is the allocated nod in sp_rule *)
		match sp_rule with 
		| Hpointsto (aa, _) ->
			Boolean.mk_not ctx (Boolean.mk_eq ctx al (alloc aa))
	in
	match sp_pred1 with
	| Hpointsto (a, _) -> (		
		let field= Expr.mk_app ctx func.field [(alloc a)] in
		let rec create_noneq to_parse =
			match to_parse with
			| first:: rest -> (noneq_rule (alloc a) first) :: create_noneq rest
			| [] -> []
		in
		field :: create_noneq rest_preds
		)

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
	let global_constr=create_global_restrictions ctx names_z3 in
	List.append pi (List.append sigma [])
	(*List.append pi (List.append sigma global_constr)*)

(* Experiments *)

let cfg = [("model", "true"); ("proof", "false")]
let ctx = (mk_context cfg)

open Solver
let z3_form1=formula_to_solver ctx form1

let solv = (mk_solver ctx None)
check solv z3_form1


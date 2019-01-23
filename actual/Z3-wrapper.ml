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
	}

let get_sl_functions_z3 ctx =
	{
	  size=FuncDecl.mk_func_decl ctx (Symbol.mk_string ctx "size") [(Integer.mk_sort ctx)] (Integer.mk_sort ctx);
	  base=FuncDecl.mk_func_decl ctx (Symbol.mk_string ctx "base") [(Integer.mk_sort ctx)] (Integer.mk_sort ctx);
	  len=FuncDecl.mk_func_decl ctx (Symbol.mk_string ctx "len") [(Integer.mk_sort ctx)] (Integer.mk_sort ctx);
	  freed=FuncDecl.mk_func_decl ctx (Symbol.mk_string ctx "freed") [(Integer.mk_sort ctx)] (Boolean.mk_sort ctx);
	}




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

let rec pi_to_solver ctx pi =
	let names_z3=get_sl_functions_z3 ctx in
	match pi with 
		| [] -> []
		| first::rest -> (expr_to_solver ctx names_z3 first) :: (pi_to_solver ctx rest)



(* Experiments *)

let cfg = [("model", "true"); ("proof", "false")]
let ctx = (mk_context cfg)

open Solver
let z3_form1=pi_to_solver ctx form1.pi
let solver = (mk_solver ctx None)
check solver z3_form1


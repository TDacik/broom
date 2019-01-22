(* in Utop use 
	#load "Formula.cmo" or #mod_use "Formula.ml" 
   	#require "z3" 
*)

open Z3
open Z3.Symbol
open Z3.Arithmetic

open Formula
let const_to_solver ctx c=
	match c with
	| Expr.Ptr a -> Integer.mk_numeral_i ctx a
	| Expr.Int a -> Integer.mk_numeral_i ctx a
	| Expr.Bool a -> Boolean.mk_val ctx a
	(*| Expr.String a -> a *)
	(* | Expr.Float a -> Real.mk_numeral_i ctx a *)
(*
let unop_to_solver o =
	match o with
	| Base -> "base"
	| Len -> "len"
	| Size -> "size"
	| Freed -> "freed"
*)


let rec expr_to_solver ctx expr =
	match expr with
	    | Expr.Var a -> Expr.mk_const ctx (Symbol.mk_string ctx (string_of_int a)) (Integer.mk_sort ctx)
	    | Expr.Const a -> const_to_solver ctx a
	    (*| Expr.UnOp (op,a) -> unop_to_string op ^ "(" ^ to_string a ^ ")"*)
	    | Expr.BinOp (op,a,b) -> 
	    	(match op with 
		| Peq ->  Boolean.mk_eq ctx (expr_to_solver ctx a) (expr_to_solver ctx b)
		| Pneq -> Boolean.mk_not ctx (Boolean.mk_eq ctx (expr_to_solver ctx a) (expr_to_solver ctx b))
		| Pless ->  Arithmetic.mk_lt ctx (expr_to_solver ctx a) (expr_to_solver ctx b)
		| Plesseq -> Arithmetic.mk_le ctx (expr_to_solver ctx a) (expr_to_solver ctx b)
	      	| Pplus -> Arithmetic.mk_add ctx [ (expr_to_solver ctx a); (expr_to_solver ctx b) ]
      		| Pminus -> Arithmetic.mk_sub ctx [ (expr_to_solver ctx a); (expr_to_solver ctx b) ]
		)
	    | Expr.Void ->  Integer.mk_numeral_i ctx (-1)
	    | Expr.Undef -> Integer.mk_numeral_i ctx (-2)

let rec pi_to_solver ctx pi =
	match pi with 
		| [] -> ""
		| first::rest -> (expr_to_solver ctx first) :: (pi_to_solver ctx rest)


(* Testcase building a simple formula with a Dlseg:
Dlseg(%l4, %l5, %l6, %l7, lambda-1:1, []) 
---------------
lambda-1:1 [%l1, %l2, %l3, ] = %l1 -(8)->%l2 * (%l1+8) -(8)->%l3 
*)
(* EXPECTED: unfolding yields  
%l4 -(8)->%l9 * (%l4+8) -(8)->%l5 * Dlseg(%l9, %l4, %l6, %l7, lambda-1:3, [])
---------------
lambda-1:3 [%l1, %l2, %l3, ] = %l1 -(8)->%l2 * (%l1+8) -(8)->%l3
*)


open Biabd
open Formula

open Biabd.Z3wrapper

let () =
	let ptr_size=Exp.Const (Int 8L) in

	let lambda = {param = [1;2;3]; form = {
		sigma = [
			Hpointsto(Var 1, ptr_size, Var 2);
			Hpointsto(BinOp(Pplus, Var 1, ptr_size), ptr_size, Var 3);
		];
		pi = [BinOp(Peq, Var 1, UnOp(Base, BinOp(Pplus, Var 1, ptr_size)))];
	};}
	in
	let result_folded = {sigma = [	Dlseg(Var 4, Var 5, Var 6, Var 7, lambda, [])];
									 pi = []}
	in
	let result_unfolded, _ = unfold_predicate result_folded 0 [] 1 in 
	print_with_lambda result_unfolded;
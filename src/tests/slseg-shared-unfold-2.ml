(* Testcase building a simple formula with a Slseg with a shared pointer which is an expression
Slseg(%l1, %l2, lambda-1:1, [(%l3+8)])  * (%l3+8) -(8)->Undef
---------------
lambda-1:1 [%l4, %l5, %l6, ] = %l4 -(8)->%l5 * (%l4+8) -(8)->%l6
*)
(* EXPECTED: unfolding yields  
(%l3+8) -(8)->Undef * %l1 -(8)->%l8 * (%l1+8) -(8)->(%l3+8) * Slseg(%l8, %l2, lambda-1:4, [(%l3+8)])
*)


open Biabd
open Formula

open Biabd.Z3wrapper

let () =
	let ptr_size=Exp.Const (Int 8L) in

	let lambda = {param = [4;5;6]; form = {
		sigma = [
			Hpointsto(Var 4, ptr_size, Var 5);
			Hpointsto(BinOp(Pplus, Var 4, ptr_size), ptr_size, Var 6);
		];
		pi = [BinOp(Peq, Var 4, UnOp(Base, BinOp(Pplus, Var 4, ptr_size)))];
	};}
	in

	let result_folded = {sigma = [	Slseg(Var 1, Var 2, lambda, [BinOp(Pplus, Var 3, ptr_size)]); 
									Hpointsto(BinOp(Pplus, Var 3, ptr_size), ptr_size, Undef)];
									 pi = []}
	in
	let result_unfolded, _ = unfold_predicate result_folded 0 [] 0 in 
	print_with_lambda result_unfolded;

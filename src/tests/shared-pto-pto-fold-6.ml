(* Testcase building a formula to shared singly-linked list:
(%l1+8) -(8)->%l4 * Slseg(%l4, %l5, lambda-1:2, [])  * (%l2+8) -(8)->%l4 * %l1 -(8)->%l2 * %l2 -(8)->%l3
---------------
lambda-1:2 [%l1, %l2, ] = %l1 -(8)->%l2*)
(* EXPECTED: abstraction yields 
Slseg(%l4, %l5, lambda-1:1, [])  * Slseg(%l1, %l3, lambda-1:2, [%l4])
---------------
lambda-1:1 [%l1, %l2, ] = %l1 -(8)->%l2
---------------
lambda-1:2 [%l1, %l2, %l6, ] = %l1 -(8)->%l2 * (%l1+8) -(8)->%l6 
*)


open Biabd
open Formula

open Biabd.Z3wrapper

let () =
	let ptr_size=Exp.Const (Int 8L) in
	let solv=config_solver () in
	let lambda = {param = [1;2]; form = {sigma = [Hpointsto(Var 1, ptr_size, Var 2)]; pi = []}} in
	let form = {
		sigma = [Hpointsto(BinOp (Pplus, Var 1, ptr_size), ptr_size, Var 4);
				 Slseg(Var 4, Var 5, lambda, []);
				 Hpointsto(BinOp (Pplus, Var 2, ptr_size), ptr_size, Var 4);
				 Hpointsto(Var 1, ptr_size,Var 2); 
				 Hpointsto(Var 2, ptr_size, Var 3);];
		pi =	[BinOp ( Peq, Var 1, UnOp (Base, BinOp (Pplus, Var 1, ptr_size)));
				 BinOp ( Peq, Var 2, UnOp (Base, BinOp (Pplus, Var 2, ptr_size)));]
	} in 
	let result = Abstraction.lseg_abstraction solv form [] in 
	print_with_lambda result;
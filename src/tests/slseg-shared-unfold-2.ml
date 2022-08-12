(* Testcase building a formula with a Slseg with %l4 as shared variable and a pointer to this Slseg but no extra pointer to %l4: 
(%l1+8) -(8)->Undef * Slseg(%l2, %l3, lambda-1:2, [%l4])  * %l4 -(8)->Undef * %l1 -(8)->%l2
---------------
lambda-1:2 [%l1, %l2, %l3, ] = %l1 -(8)->%l2 * (%l1+8) -(8)->%l3
*)
(* EXPECTED: abstraction does not work -> no changes to formula are made
*)

open Biabd
open Formula

open Biabd.Z3wrapper

let () =
	let ptr_size=Exp.Const (Int 8L) in
	let lambda = {param= [1;2;3]; 
					form = {
							sigma = [
									Hpointsto(Var 1, ptr_size, Var 2);
									Hpointsto(BinOp (Pplus, Var 1, ptr_size), ptr_size, Var 3) ]; 
							pi = [BinOp ( Peq, Var 1, UnOp (Base, BinOp (Pplus, Var 1, ptr_size)));]}} in
	let form = {
		
		sigma = [Hpointsto(BinOp (Pplus, Var 1, ptr_size), ptr_size, Undef);
				 Slseg(Var 2, Var 3, lambda, [Var 4]);
				 Hpointsto(Var 4, ptr_size, Undef);
				 Hpointsto(Var 1, ptr_size,Var 2); 
				];
				 (* need the following equivalences to allow to infer a suitable lambda*)
		pi =	[BinOp ( Peq, Var 1, UnOp (Base, BinOp (Pplus, Var 1, ptr_size)));]
	} in 
	let solv=config_solver () in
	let result = Abstraction.lseg_abstraction solv form [] in 
	print_with_lambda result;
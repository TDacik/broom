
(* Testcase building a formula with a Dlseg with %l5 as shared variable and two pointer to/from this Dlseg and a pointer to %l5: 
%l4 -(8)->%l1 * (%l4+8) -(8)->%l6 * (%l4+16) -(8)->%l5 * Dlseg(%l1, %l4, %l2, %l3, lambda-1:4, [%l5])  * %l5 -(8)->Undef
---------------
lambda-1:4 [%l1, %l2, %l3, %l4, ] = %l1 -(8)->%l2 * (%l1+8) -(8)->%l3 * (%l1+16) -(8)->%l4
*)
(* EXPECTED: abstraction yields formula of form 
%l5 -(8)->Undef * Dlseg(%l4, %l6, %l2, %l3, lambda-1:2, [%l5])
---------------
lambda-1:2 [%l4, %l1, %l9, %l7, ] = %l4 -(8)->%l1 * (%l4+8) -(8)->%l9 * (%l4+16) -(8)->%l7
*)

open Biabd
open Formula

open Biabd.Z3wrapper

let () =
	let ptr_size=Exp.Const (Int 8L) in
	let ptr_size2 = Exp.Const (Int 16L) in
	let lambda = {param= [1;2;3;4]; 
					form = {
							sigma = [
									Hpointsto(Var 1, ptr_size, Var 2);
									Hpointsto(BinOp (Pplus, Var 1, ptr_size), ptr_size, Var 3);
									Hpointsto(BinOp (Pplus, Var 1, ptr_size2), ptr_size, Var 4) ]; 
							pi =	[BinOp ( Peq, Var 1, UnOp (Base, BinOp (Pplus, Var 1, ptr_size)));
									 BinOp ( Peq, Var 1, UnOp (Base, BinOp (Pplus, Var 1, ptr_size2)));
									 ]}} in
	let form = {
		
		sigma = [Hpointsto(Var 4, ptr_size, Var 1);
				 Hpointsto(BinOp (Pplus, Var 4, ptr_size), ptr_size, Var 6);
				 Hpointsto(BinOp (Pplus, Var 4, ptr_size2), ptr_size, Var 5);
				 Dlseg(Var 1, Var 4, Var 2, Var 3, lambda, [Var 5]);
				 Hpointsto(Var 5, ptr_size, Undef);
				];
				 (* need the following equivalences to allow to infer a suitable lambda*)
		pi =	[BinOp ( Peq, Var 4, UnOp (Base, BinOp (Pplus, Var 4, ptr_size)));
				 BinOp ( Peq, Var 4, UnOp (Base, BinOp (Pplus, Var 4, ptr_size2)))]
	} in 
	let solv=config_solver () in
	let result = Abstraction.lseg_abstraction solv form [] in 
	print_with_lambda result;
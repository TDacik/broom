(* Testcase building a simple formula with pointers to shared variable %l4 of form 
(%l1+8) -(8)->%l4 * (%l2+8) -(8)->%l4 * %l4 -(8)->Undef * %l1 -(8)->%l2 * %l2 -(8)->%l3
*)
(* EXPECTED: abstraction yields formula of form 
%l4 -(8)->Undef * Slseg(%l1, %l3, lambda-1:2, [%l4])
---------------
lambda-1:2 [%l1, %l2, %l5, ] = %l1 -(8)->%l2 * (%l1+8) -(8)->%l5
*)


open Biabd
open Formula

open Biabd.Z3wrapper

let () =
	let ptr_size=Exp.Const (Int 8L) in
	let solv=config_solver () in

	let form = {
		sigma = [Hpointsto(BinOp (Pplus, Var 1, ptr_size), ptr_size, Var 4);
				 Hpointsto(BinOp (Pplus, Var 2, ptr_size), ptr_size, Var 4);
				 Hpointsto(Var 4, ptr_size, Undef);
				 Hpointsto(Var 1, ptr_size,Var 2); 
				 Hpointsto(Var 2, ptr_size, Var 3);];
		pi =	[BinOp ( Peq, Var 1, UnOp (Base, BinOp (Pplus, Var 1, ptr_size)));
				 BinOp ( Peq, Var 2, UnOp (Base, BinOp (Pplus, Var 2, ptr_size)));
				]
	} in 
	let result = Abstraction.lseg_abstraction solv form [4] in 
	print_with_lambda result ;
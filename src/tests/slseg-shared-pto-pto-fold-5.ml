(* Testcase building a formula to shared node where it can only be semantically deriven that node is shared:
(%l1+8) -(8)->%l4 * (%l2+8) -(8)->%l5 * %l4 -(8)->Undef * %l1 -(8)->%l2 * %l2 -(8)->%l3 & (%l4=%l5)*)
(* EXPECTED: abstraction yields 
%l4 -(8)->Undef * Slseg(%l1, %l3, lambda-1:2, [%l4]) & (%l4=%l5)
---------------
lambda-1:2 [%l1, %l2, %l6, ] = %l1 -(8)->%l2 * (%l1+8) -(8)->%l6
*)


open Biabd
open Formula

open Biabd.Z3wrapper

let () =
	let ptr_size=Exp.Const (Int 8L) in
	let solv=config_solver () in

	let form = {
		sigma = [Hpointsto(BinOp (Pplus, Var 1, ptr_size), ptr_size, Var 4);
				 Hpointsto(BinOp (Pplus, Var 2, ptr_size), ptr_size, Var 5);
				 Hpointsto(Var 4, ptr_size, Undef);
				 Hpointsto(Var 1, ptr_size,Var 2); 
				 Hpointsto(Var 2, ptr_size, Var 3);];
		pi =	[BinOp ( Peq, Var 1, UnOp (Base, BinOp (Pplus, Var 1, ptr_size)));
				 BinOp ( Peq, Var 2, UnOp (Base, BinOp (Pplus, Var 2, ptr_size)));
				 BinOp ( Peq, Var 4, Var 5)
				]
	} in
	print_with_lambda form;
	let result = Abstraction.lseg_abstraction solv form [] in 
	print_with_lambda result;
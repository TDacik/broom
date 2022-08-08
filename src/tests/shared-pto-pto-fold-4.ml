(* Testcase building a formula with two shared pointers to %l4 and %l5:
(%l1+8) -(8)->%l4 * (%l1+16) -(8)->%l5 * (%l2+8) -(8)->%l4 * (%l2+16) -(8)->%l5 * %l4 -(8)->Undef * %l5 -(8)->Undef * %l1 -(8)->%l2 * %l2 -(8)->%l3
*)
(* EXPECTED: abstraction yields 
%l4 -(8)->Undef * %l5 -(8)->Undef * Slseg(%l1, %l3, lambda-1:3, [%l4, %l5])
---------------
lambda-1:3 [%l1, %l2, %l7, %l6, ] = %l1 -(8)->%l2 * (%l1+8) -(8)->%l7 * (%l1+16) -(8)->%l6
*)


open Biabd
open Formula

open Biabd.Z3wrapper

let () =
	let ptr_size=Exp.Const (Int 8L) in
	let ptr_size2 = Exp.Const (Int 16L) in
	let solv=config_solver () in

	let form = {
		sigma = [Hpointsto(BinOp (Pplus, Var 1, ptr_size), ptr_size, Var 4);
				 Hpointsto(BinOp (Pplus, Var 1, ptr_size2), ptr_size, Var 5);
				 Hpointsto(BinOp (Pplus, Var 2, ptr_size), ptr_size, Var 4);
				 Hpointsto(BinOp (Pplus, Var 2, ptr_size2), ptr_size, Var 5);
				 Hpointsto(Var 4, ptr_size, Undef);
				 Hpointsto(Var 5, ptr_size, Undef);
				 Hpointsto(Var 1, ptr_size,Var 2); 
				 Hpointsto(Var 2, ptr_size, Var 3);];
		pi =	[BinOp ( Peq, Var 1, UnOp (Base, BinOp (Pplus, Var 1, ptr_size)));
				 BinOp ( Peq, Var 1, UnOp (Base, BinOp (Pplus, Var 1, ptr_size2)));
				 BinOp ( Peq, Var 2, UnOp (Base, BinOp (Pplus, Var 2, ptr_size)));
				 BinOp ( Peq, Var 2, UnOp (Base, BinOp (Pplus, Var 2, ptr_size2)));
				]
	} in
	let result = Abstraction.lseg_abstraction solv form [] in 
	print_with_lambda result ;
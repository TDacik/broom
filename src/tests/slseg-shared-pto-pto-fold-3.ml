(* Testcase building a formula with shared pointer to %l4 and pointer to data node:
(%l1+8) -(8)->%l4 * (%l1+16) -(8)->%l5 * (%l2+8) -(8)->%l4 * (%l2+16) -(8)->%l6 * %l4 -(8)->Undef * %l5 -(8)->5 * %l6 -(8)->6 * %l1 -(8)->%l2 * %l2 -(8)->%l3
*)
(* EXPECTED: abstraction yields 
%l4 -(8)->Undef * Slseg(%l1, %l3, lambda-1:2, [%l4])
---------------
lambda-1:2 [%l1, %l2, %l7, ] = %l1 -(8)->%l2 * (%l1+8) -(8)->%l7 * (%l1+16) -(8)->%l5 * %l5 -(8)->Undef
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
				 Hpointsto(BinOp (Pplus, Var 2, ptr_size2), ptr_size, Var 6);
				 Hpointsto(Var 4, ptr_size, Undef);
				 Hpointsto(Var 5, ptr_size, Const(Int 5L));
				 Hpointsto(Var 6, ptr_size, Const(Int 6L));
				 Hpointsto(Var 1, ptr_size,Var 2); 
				 Hpointsto(Var 2, ptr_size, Var 3);];
		pi =	[BinOp ( Peq, Var 1, UnOp (Base, BinOp (Pplus, Var 1, ptr_size)));
				 BinOp ( Peq, Var 1, UnOp (Base, BinOp (Pplus, Var 1, ptr_size2)));
				 BinOp ( Peq, Var 2, UnOp (Base, BinOp (Pplus, Var 2, ptr_size)));
				 BinOp ( Peq, Var 2, UnOp (Base, BinOp (Pplus, Var 2, ptr_size2)));
				]
	} in
	let result = Abstraction.lseg_abstraction solv form [] in 
	print_with_lambda result;
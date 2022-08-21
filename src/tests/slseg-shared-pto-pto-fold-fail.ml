(* Testcase building a formula with non-shared pointers but to same block:
(%l1+8) -(8)->%l4 * (%l2+8) -(8)->(8+%l4) * %l4 -(8)->Undef * (8+%l4) -(8)->Undef * %l1 -(8)->%l2 * %l2 -(8)->%l3 * %l3 -(8)->%l5
*)
(* EXPECTED: abstraction fails
*)


open Biabd
open Formula

open Biabd.Z3wrapper

let () =
	let ptr_size=Exp.Const (Int 8L) in
	let solv=config_solver () in

	let form = {
		sigma = [Hpointsto(BinOp (Pplus, Var 1, ptr_size), ptr_size, Var 4);
				 Hpointsto(BinOp (Pplus, Var 2, ptr_size), ptr_size, BinOp(Pplus, ptr_size, Var 4));
				 Hpointsto(Var 4, ptr_size, Undef);
				 Hpointsto(BinOp(Pplus, ptr_size, Var 4), ptr_size, Undef);
				 Hpointsto(Var 1, ptr_size,Var 2); 
				 Hpointsto(Var 2, ptr_size, Var 3);
				 Hpointsto(Var 3, ptr_size, Var 5);];
		pi =	[BinOp ( Peq, Var 1, UnOp (Base, BinOp (Pplus, Var 1, ptr_size)));
				 BinOp ( Peq, Var 2, UnOp (Base, BinOp (Pplus, Var 2, ptr_size)));
				 BinOp ( Peq, Var 4, UnOp (Base, BinOp (Pplus, Var 4, ptr_size)));
				]
	} in
	let result = Abstraction.lseg_abstraction solv form [] in 
	print_with_lambda result ;
(* Testcase building a formula with nodes containg fields which point back to the node
*)
(* EXPECTED: abstraction yields 
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
		sigma = [Hpointsto(BinOp (Pplus, Var 1, ptr_size), ptr_size, Var 1);
				 Hpointsto(BinOp (Pplus, Var 2, ptr_size), ptr_size, Var 2);
				 Hpointsto(Var 1, ptr_size,Var 2); 
				 Hpointsto(Var 2, ptr_size, Var 3);];
		pi =	[BinOp ( Peq, Var 1, UnOp (Base, BinOp (Pplus, Var 1, ptr_size)));
				 BinOp ( Peq, Var 2, UnOp (Base, BinOp (Pplus, Var 2, ptr_size)));
				]
	} in
	let result = Abstraction.lseg_abstraction solv form [] in 
	print_with_lambda result;
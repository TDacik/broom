(* Testcase building a simple formula with 4 pointers describing a Dlseg with a shared data element:
%l1 -(8)->%l2 * (%l1+8) -(8)->%l4 * (%l1+16) -(8)->%l5 * %l2 -(8)->%l3 * (%l2+8) -(8)->%l1 * (%l2+16) -(8)->%l5 * %l5 -(8)->Undef
*)
(* EXPECTED: abstraction yields formula of form 
%l5 -(8)->Undef * Dlseg(%l1, (%l4+8), %l2, (%l3+8), lambda-1:2, [%l5])
---------------
lambda-1:2 [%l2, %l7, %l1, %l6, ] = (%l2+8) -(8)->%l1 * %l2 -(8)->%l7 * (%l2+16) -(8)->%l6
*)

open Biabd
open Formula

open Biabd.Z3wrapper

let () =
	let ptr_size=Exp.Const (Int 8L) in
	let ptr_size2 = Exp.Const (Int 16L) in
	
	let form = {
		sigma = [Hpointsto(Var 1, ptr_size,Var 2); 
				 Hpointsto(BinOp(Pplus, Var 1, ptr_size), ptr_size,Var 4);
				 Hpointsto(BinOp(Pplus, Var 1, ptr_size2), ptr_size, Var 5);
				 Hpointsto(Var 2, ptr_size, Var 3);
				 Hpointsto(BinOp(Pplus, Var 2, ptr_size), ptr_size,Var 1);
				 Hpointsto(BinOp(Pplus, Var 2, ptr_size2), ptr_size, Var 5);
				 Hpointsto(Var 5, ptr_size, Undef);];
		pi =	[BinOp ( Peq, Var 1, UnOp (Base, BinOp (Pplus, Var 1, ptr_size)));
				 BinOp ( Peq, Var 1, UnOp (Base, BinOp (Pplus, Var 1, ptr_size2)));
				 BinOp ( Peq, Var 2, UnOp (Base, BinOp (Pplus, Var 2, ptr_size)));
				 BinOp ( Peq, Var 2, UnOp (Base, BinOp (Pplus, Var 2, ptr_size2)));]
	} in 
	let solv=config_solver () in
	let result = Abstraction.lseg_abstraction solv form [] in
	print_with_lambda result; 

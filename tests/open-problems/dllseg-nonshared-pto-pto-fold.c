(* Testcase building a simple formula with 4 pointers describing a Dlseg:
%l1 -(8)->%l2 * (%l1+8) -(8)->%l4 * %l2 -(8)->%l3 * (%l2+8) -(8)->%l1
*)
(* EXPECTED: abstraction yields formula of form 
Dlseg(%l1, %l4, %l2, %l3, [])
---------------
lambda-1:2 [%l1, %l2, %l3, ] = %l1 -(8)->%l3 * (%l1+8) -(8)->%l2
*)

open Biabd
open Formula

open Biabd.Z3wrapper

let () =
	let ptr_size=Exp.Const (Int 8L) in
	
	let form = {
		sigma = [Hpointsto(Var 1, ptr_size,Var 2); 
				 Hpointsto(BinOp(Pplus, Var 1, ptr_size), ptr_size,Var 4);
				 Hpointsto(Var 2, ptr_size, Var 3);
				 Hpointsto(BinOp(Pplus, Var 2, ptr_size), ptr_size,Var 1);];
		pi =	[BinOp ( Peq, Var 1, UnOp (Base, BinOp (Pplus, Var 1, ptr_size)));
				 BinOp ( Peq, Var 2, UnOp (Base, BinOp (Pplus, Var 2, ptr_size)));]
	} in 
	let solv=config_solver () in
	let result = Abstraction.lseg_abstraction solv form [] in
	print_with_lambda result; 

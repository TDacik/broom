open Biabd
open Formula

open Biabd.Z3wrapper
(* Testcase building a formula where nodes point to a nested node which itself points back to the 
top level node: (%l1+8) -(8)->%l4 * (%l2+8) -(8)->%l5 * %l1 -(8)->%l2 * %l2 -(8)->%l3 * %l4 -(8)->%l1 * %l5 -(8)->%l2*)
(* EXPECTED: abstraction yields Slseg(%l1,%l2,lambda,[]) with
lambda(a,b)= a -(8)-> b * a+8 -(8)->c * c -(8)->a *)

let () =
	let ptr_size=Exp.Const (Int 8L) in
	let lambda = {
			param = [1;2];
			form = {
				sigma = [Hpointsto(Var 1, ptr_size, Var 2)];
				pi=[]
				}
			} in
	
	let form = {
		sigma = [Hpointsto(BinOp (Pplus, Var 1, ptr_size), ptr_size, Var 4);
				 Hpointsto(BinOp (Pplus, Var 2, ptr_size), ptr_size, Var 5); 
				 Hpointsto(Var 1, ptr_size,Var 2); 
				 Hpointsto(Var 2, ptr_size, Var 3);
				 Hpointsto(Var 4, ptr_size, Var 1);
				 Hpointsto(Var 5, ptr_size, Var 2);
				 ];
				 (* need the following equivalences to allow to infer a suitable lambda*)
		pi =	[BinOp ( Peq, Var 1, UnOp (Base, BinOp (Pplus, Var 1, ptr_size)));
				 BinOp ( Peq, Var 2, UnOp (Base, BinOp (Pplus, Var 2, ptr_size)));]
	} in 
	let solv=config_solver () in
	print_string "\n Test 1\n";
	let result,_ = Abstraction.lseg_abstraction solv form [] in 
	print_with_lambda result;

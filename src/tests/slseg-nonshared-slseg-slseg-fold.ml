(* example with a nested ls0+ and nested 1+ *)
(* EXPECTED: abstraction golds into a list with lambda for nested ls0+ *)

open Biabd
open Formula

open Biabd.Z3wrapper

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
				 Slseg(Var 4, Var 6, lambda, []);
				 Slseg(Var 5, Var 7, lambda, []);
				 ];
				 (* need the following equivalences to allow to infer a suitable lambda*)
		pi =	[BinOp ( Pneq, Var 4, Var 6);
				 BinOp ( Peq, Var 6, Const(Ptr 0));
				 BinOp ( Peq, Var 7, Const(Ptr 0));
				 BinOp ( Peq, Var 1, UnOp (Base, BinOp (Pplus, Var 1, ptr_size)));
				 BinOp ( Peq, Var 2, UnOp (Base, BinOp (Pplus, Var 2, ptr_size)));]
	} in 
	let solv=config_solver () in
	print_string "\n Test 1\n";
	let result,_ = Abstraction.lseg_abstraction solv form [] in 
	print_with_lambda result;

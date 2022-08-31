open Biabd
open Formula

open Biabd.Z3wrapper

let () =
	let ptr_size=Exp.Const (Int 8L) in
	
	let form = {
		sigma = [Hpointsto(BinOp (Pplus, Var 1, ptr_size), ptr_size, Var 4);
				 Hpointsto(BinOp (Pplus, Var 2, ptr_size), ptr_size, Var 4);
				 Hpointsto(Var 4, Const(Int 20L), Undef); (* point to data block with 20 allocated bytes *)
				 (*Hpointsto(Var 5, Const(Int 20L), Undef);*) (* point to data block with 20 allocated bytes *)
				 Hpointsto(Var 1, ptr_size,Var 2); 
				 Hpointsto(Var 2, ptr_size, Var 3);];
				 (* need the following equivalences to allow to infer a suitable lambda*)
		pi =	[BinOp ( Peq, Var 1, UnOp (Base, BinOp (Pplus, Var 1, ptr_size)));
				 BinOp ( Peq, Var 2, UnOp (Base, BinOp (Pplus, Var 2, ptr_size)));]
	} in 
	let solv=config_solver () in
	print_string "\n Test 1\n";
	let result,_ = Abstraction.lseg_abstraction solv form [] in 
	print_with_lambda result;
	(*
	let form_top_value = {
		sigma = [Hpointsto(BinOp (Pplus, Var 1, ptr_size), ptr_size, Const (Int 1234L));
				 Hpointsto(BinOp (Pplus, Var 2, ptr_size), ptr_size, Undef);
				 Hpointsto(Var 1, ptr_size,Var 2); 
				 Hpointsto(Var 2, ptr_size, Var 3);];
				 (* need the following equivalences to allow to infer a suitable lambda*)
		pi =	[BinOp ( Peq, Var 1, UnOp (Base, BinOp (Pplus, Var 1, ptr_size)));
				 BinOp ( Peq, Var 2, UnOp (Base, BinOp (Pplus, Var 2, ptr_size)));]
	} in 
	print_string "\n Test 2\n";
	let result = Abstraction.lseg_abstraction solv form_top_value [1] in 
	print_with_lambda result;
*)

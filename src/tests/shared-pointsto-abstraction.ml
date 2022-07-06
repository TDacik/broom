(* Testcase with a formula describing two nodes pointing to a shared data elem which is abstracted*)
(* EXPECTED: the two points-to predicates are abstracted to a Slseg with a shared pointer to T[20]*)

open Biabd
open Formula
open Biabd.Z3wrapper


let () = 
	print_string "\ntestcase shared-pointsto-abstraction\n";

	let ptr_size=Exp.Const (Exp.Int (Int64.of_int 8)) in

	let form = {
		sigma = [Hpointsto(BinOp (Pplus, Var 1, ptr_size), ptr_size, Var 4);
				 Hpointsto(BinOp (Pplus, Var 2, ptr_size), ptr_size, Var 4);
				 Hpointsto(Var 4, Const(Int 20L), Undef); (* point to data block with 20 allocated bytes *)
				 Hpointsto(Var 1, ptr_size,Var 2); 
				 Hpointsto(Var 2, ptr_size, Var 3);];
				 (* need the following equivalences to allow to infer a suitable lambda*)
		pi =	[BinOp ( Peq, Var 1, UnOp (Base, BinOp (Pplus, Var 1, ptr_size)));
				 BinOp ( Peq, Var 2, UnOp (Base, BinOp (Pplus, Var 2, ptr_size)));]
	}
	in 
	let solv=config_solver () in
	let res = Abstraction.lseg_abstraction solv form [1] in 
	print_with_lambda form;
	print_with_lambda res; 

(* Testcase building a simple formula with a Slseg with one shared node and a lambda containing 
containing a pointer to this shared node (%l3)*)
(* EXPECTED: no fresh variable introduced by unfolding %l1+8 -> %l3 for %l3, so %l3 should be reused *)

open Biabd
open Formula


let () = 
	print_string "\ntestcase shared-slseg-unfold\n";

	let ptr_size=Exp.Const (Exp.Int (Int64.of_int 8)) in

	let lambda= {param=[1;2] ;form={
      sigma = [ Hpointsto (Var 1, ptr_size, Var 2); Hpointsto (BinOp ( Pplus, Var 1, ptr_size), ptr_size, Var 3)]; pi=[] }}
	in 
	let form = {sigma = [Slseg (Var 5, Var 6, lambda, [Var 3]);
						 Hpointsto(Var 4, ptr_size, Var 5);
						 Hpointsto(BinOp ( Pplus, Var 4, ptr_size), ptr_size, Var 3);];
	  				pi=[]} 
	in 
	let res,_ = Formula.unfold_predicate form 0 [] 0 in
	print_with_lambda form;
	print_with_lambda res; 

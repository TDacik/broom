(* * * * * * * * * * * * * * * main * * * * * * * * * * * * * * *)

(*
let () =
	let fnc_tbl = Biabd.SpecTable.create in
	let rec exec tbl fncs =
		match fncs with
		| [] -> ()
		| (_, fnc)::tl -> Biabd.SymExecution.exec_fnc tbl fnc; exec tbl tl
	in
	exec fnc_tbl CL.Util.stor.fncs;
	print_endline "===============================================";
	Biabd.SpecTable.print fnc_tbl
*)

open Biabd.Formula
open Biabd.Z3wrapper
open Biabd.Abduction

let() =
	let ptr_size=Exp.Const (Exp.Int (Int64.of_int 8)) in
	let solv=config_solver () in
	 print_string "ahoj";
	 let form1 =
	    let lambda= {param=[1;2;3] ;form={
	      	sigma = [ Hpointsto (Var 1, ptr_size, Var 2); Hpointsto (BinOp ( Pplus, Var 1, ptr_size), ptr_size, Var 3)  ]; 
		pi=[BinOp ( Peq, Var 1, UnOp ( Base, Var 1));BinOp ( Peq, UnOp ( Len, Var 1), Const (Int (Int64.of_int 16)));] }}
	    in
	    {
   		 sigma = [ Dlseg (Var 10, Const (Ptr 0), Var 11,Const (Ptr 0),  lambda)];
		 pi = []
	    }
	 in
	 let form2 =
	    let lambda= {param=[1;2;3] ;form={
	      	sigma = [ Hpointsto (Var 1, ptr_size, Var 2); Hpointsto (BinOp ( Pplus, Var 1, ptr_size), ptr_size, Var 3)  ]; pi=[] }}
	    in
	    let lambdasll= {param=[1;2] ;form={
	      	sigma = [ Hpointsto (Var 1, ptr_size, Var 2)];	pi=[] }}
	    in

	    {
   		 sigma = [ Dlseg (Var 10, Const (Ptr 0), Var 11,Var 12,  lambda); Dlseg (Var 12, Const (Ptr 0), Var 14, Var 13,  lambda);
		 Hpointsto (Var 13, ptr_size, Var 2); Slseg (Var 24, Var 10,lambdasll)];
		 pi = [BinOp ( Pneq, Var 10,Var 12 );BinOp ( Pneq, Var 12,Var 13);]
	    }
	 in
	print_with_lambda form1;
	(*print_with_lambda form2;
	let q=formula_to_solver solv.ctx form2 in
	if (Z3.Solver.check solv.solv q)==SATISFIABLE then print_string "OK" else print_string "FAIL"*)
	(*let form_unf,_=unfold_predicate form1 0 [] 2 in
	let form_unf2,_=unfold_predicate form_unf 2 [] 2 in
	print_with_lambda form_unf2*)
	match (apply_match solv (0,0) 30 form1 form2 [] 2) with
    	| ApplyOK (f1,f2,added_lvars) ->
		print f1;
		print f2;




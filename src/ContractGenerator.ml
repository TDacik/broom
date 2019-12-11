
open Biabd.Formula

let ptr_size=Exp.Const (Int 8L)

let form1 = {
    sigma = [ Hpointsto (Var 1, ptr_size, Var 2) ];
    pi = [ BinOp ( Peq, Var 1, UnOp ( Base, Var 1));
          BinOp ( Peq, UnOp ( Len, Var 1), Const (Int 8L));
          BinOp ( Peq, Var 1, Var 2332 );
          BinOp ( Peq, Var 2, Const (Ptr 0)) ]
    (*evars = [ 2 ]*)
}


let get_contract _ (* insn *) = ("pre", "post")

let custom_fnc insn =
	let (pre, post) = get_contract insn in
		Printf.printf "%s\n" pre;
		CL.Printer.print_insn insn;
		Printf.printf "%s\n" post





(* * * * * * * * * * * * * * * main * * * * * * * * * * * * * * *)
let () =
	List.iter CL.Printer.print_fnc CL.Util.stor.fncs;
	(* List.iter Printer.custom_fnc Util.stor.fncs; *)
	print_newline ();
	Printf.printf "%s\n" (to_string form1)

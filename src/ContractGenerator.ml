
open Biabd.Formula
module Contract = Biabd.Contract

let ptr_size=Exp.Const (Int 8L)

let form1 = {
    sigma = [ Hpointsto (Var 1, ptr_size, Var 2) ];
    pi = [ BinOp ( Peq, Var 1, UnOp ( Base, Var 1));
          BinOp ( Peq, UnOp ( Len, Var 1), Const (Int 8L));
          BinOp ( Peq, Var 1, Var 2332 );
          BinOp ( Peq, Var 2, Const (Ptr 0)) ]
    (*evars = [ 2 ]*)
}

let custom_fnc insn =
	let lc = Contract.get_contract insn in
		CL.Printer.print_insn insn;
		CL.Util.print_list Contract.to_string lc

let rec print_storage fncs =
	match fncs with
	| [] -> ()
	| (_, f)::tl -> if CL.Util.is_fnc_static f then Printf.printf "static ";
		let str = CL.Printer.get_fnc_name f in
			Printf.printf "%s(" str;
			CL.Util.print_list CL.Printer.var_to_string f.args;
			Printf.printf "):\n";
			(match f.cfg with
				| Some bbs -> CL.Printer.print_cfg custom_fnc bbs
				| None -> ());
			print_storage tl



(* * * * * * * * * * * * * * * main * * * * * * * * * * * * * * *)
let () =
	(* List.iter CL.Printer.print_fnc CL.Util.stor.fncs; *)
	
	print_storage CL.Util.stor.fncs;
	print_newline ();
	Printf.printf "%s\n" (to_string form1)

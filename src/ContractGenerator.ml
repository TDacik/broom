
module Contract = Biabd.Contract

let custom_fnc insn =
	let lc = Contract.get_contract insn in
		CL.Printer.print_insn insn;
		CL.Util.print_list Contract.to_string lc

let rec print_storage fncs =
	match fncs with
	| [] -> ()
	| (_, f)::tl -> CL.Printer.print_fnc_declaration f;
			Printf.printf ":\n";
			CL.Printer.print_cfg custom_fnc f.cfg;
			print_storage tl

(* * * * * * * * * * * * * * * main * * * * * * * * * * * * * * *)
let () =
	(* List.iter CL.Printer.print_fnc CL.Util.stor.fncs; *)
	
	print_storage CL.Util.stor.fncs
	(* print_newline ();
	Printf.printf "%s\n" (to_string form1) *)

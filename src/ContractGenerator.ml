
module Contract = Biabd.Contract

let custom_fnc insn =
	CL.Printer.print_insn insn;
	let lc = Contract.get_contract insn in
	CL.Util.print_list_endline Contract.to_string lc

let rec print_storage fncs =
	match fncs with
	| [] -> ()
	| (_, f)::tl -> CL.Printer.print_fnc_declaration f;
		print_endline ":";
		CL.Printer.print_cfg custom_fnc f.cfg;
		print_storage tl

(* * * * * * * * * * * * * * * main * * * * * * * * * * * * * * *)
let () = print_storage CL.Util.stor.fncs

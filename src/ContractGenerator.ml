
module Contract = Biabd.Contract

let custom_fnc insn =
	CL.Printer.print_insn insn;
	let lc = Contract.get_contract insn in
	CL.Util.print_list (fun x -> "\n"^(Contract.to_string x)) lc; print_newline ()

let rec print_storage fncs =
	match fncs with
	| [] -> ()
	| (_, f)::tl -> CL.Printer.print_fnc_declaration f;
		print_endline ":";
		CL.Printer.print_cfg custom_fnc f.cfg;
		print_storage tl

(* * * * * * * * * * * * * * * main * * * * * * * * * * * * * * *)
let () = print_storage CL.Util.stor.fncs






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
	print_newline ()

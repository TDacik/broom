




let get_contract insn = ("pre", "post")

let custom_fnc insn =
	let (pre, post) = get_contract insn in
		Printf.printf "%s\n" pre;
		Printer.print_insn insn;
		Printf.printf "%s\n" post





(* * * * * * * * * * * * * * * main * * * * * * * * * * * * * * *)
let () =
	List.iter Printer.print_fnc Util.stor.fncs;
	(* List.iter Printer.custom_fnc Util.stor.fncs; *)
	print_newline ()

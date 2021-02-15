(* * * * * * * * * * * * * * * main * * * * * * * * * * * * * * *)


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




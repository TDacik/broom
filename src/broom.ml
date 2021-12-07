open Biabd
(* * * * * * * * * * * * * * * main * * * * * * * * * * * * * * *)

let custom_fnc insn =
	CL.Printer.print_insn insn;
	if Config.print_contracts () then (
		let lc = Contract.get_contract insn in
		CL.Util.print_list_endline Contract.to_string lc
	)

let rec print_storage fncs =
	match fncs with
	| [] -> ()
	| (_, f)::tl ->
		print_endline ((CL.Printer.fnc_declaration_to_string f)^":");
		CL.Printer.print_cfg custom_fnc f.cfg;
		print_storage tl

let print_program () = print_storage CL.Util.stor.fncs 

(* * * * * * * * * * * * * * * main * * * * * * * * * * * * * * *)
let () =
	Config.analyse_cmd_arguments ();
	if Config.print_cl () || Config.print_contracts () then
		print_program (); print_newline ();
	if Config.dry_run () then
		exit 0;
	let fnc_tbl = SpecTable.create in
	let rec exec tbl fncs =
		match fncs with
		| [] -> ()
		| (_, fnc)::tl -> SymExecution.exec_fnc tbl fnc; exec tbl tl
	in
	exec fnc_tbl CL.Util.stor.fncs;
	print_endline "===============================================";
	Biabd.SpecTable.print fnc_tbl;
	print_endline "===============================================";
	if Config.stats () then
		Biabd.Config.display_stats ();

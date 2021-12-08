(*
 *  Copyright (C) Broom team
 *
 *  This file is part of Broom.
 *
 *  Broom is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  Broom is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <https://www.gnu.org/licenses/>.
 *)

open Biabd

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

let print_file () = print_storage CL.Util.stor.fncs

(* * * * * * * * * * * * * * * main * * * * * * * * * * * * * * *)
let () =
	Config.analyse_cmd_arguments ();
	if Config.print_cl () || Config.print_contracts () then
		print_file (); print_newline ();
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
	Biabd.Config.display_stats ();

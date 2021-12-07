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

type cl_uid = CL.Loc.cl_uid

(*
  key is a unique uid of function
  value is list of contracts (pre, post1), (pre, post2)
        // or (pre, [post1,post2])... ?
*)

type t = (cl_uid, Contract.t list) Hashtbl.t

let create = let (fnc_tbl : t) = Hashtbl.create 1 in fnc_tbl

(* TODO change value to mutable? *)
let add tbl uid contracts =
	let found = Hashtbl.find_opt tbl uid in
	match found with
	| None -> Hashtbl.add tbl uid contracts
	| Some c -> Hashtbl.replace tbl uid (c @ contracts) (* TODO join *)

let only_add tbl uid contracts =
	let remove_ok_contracts con =
		if (Contract.is_OK con) then None else Some con
	in
	let found = Hashtbl.find_opt tbl uid in
	match found with
	| None -> Hashtbl.add tbl uid contracts
	| Some c ->
		let stay = List.filter_map remove_ok_contracts c in
		Hashtbl.replace tbl uid (stay @ contracts)

let find_opt tbl x = Hashtbl.find_opt tbl x

(** printing on standard output *)

let print_spec uid contracts =
	let fnc_decl = CL.Printer.fnc_declaration_to_string (CL.Util.get_fnc uid) in
	print_endline (">>> spec of function " ^ fnc_decl ^ ":");
	CL.Util.print_list_endline (Contract.to_string ~not_unfinished:true) contracts

let print tbl =
	print_endline ("FUNCTIONS: " ^ (Int.to_string (Hashtbl.length tbl)));
	Hashtbl.iter print_spec tbl

let reset = Hashtbl.reset

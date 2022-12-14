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

(* Useful functions for Code Listener Storage *)

module AGU = Atdgen_runtime.Util

open Type
open Operand

(* FIXME: read-only global variable? *)
let stor = AGU.Json.from_channel Storage.read_t stdin

let get_fnc uid = List.assoc uid stor.Storage.fncs

let get_fnc_opt uid = List.assoc_opt uid stor.Storage.fncs

let get_type uid = List.assoc uid stor.Storage.types

let get_var uid = List.assoc uid stor.Storage.vars

let get_var_opt uid = List.assoc_opt uid stor.Storage.vars

let list_diff l1 l2 = List.filter (fun x -> not (List.mem x l2)) l1

let list_inter l1 l2 = List.filter (fun x -> (List.mem x l2)) l1

(* add missing elements of list l1 to l2 *)
let rec list_join_unique l1 l2 =
	let mem x =
		let eq y= (x=y) in
		List.exists eq l2
	in
	match l1 with
	| [] -> l2
	| first::rest ->
		if mem first
		then list_join_unique rest l2
		else list_join_unique rest (first::l2)

(* find max positive number in list *)
let rec list_max_positive l =
	match l with
	| [] -> 0
	| n::tl -> max n (list_max_positive tl)

let rec list_to_string to_string args =
	match args with
	| [] -> ""
	| lst::[] -> to_string lst
	| hd::tl -> (to_string hd) ^ ", " ^ (list_to_string to_string tl)

(* Print list of elms separated by delim (default ', ') calling 'to_string' on
   each elm *)
let rec print_list ?delim:(delim=", ") ?oc:(oc=stdout) to_string args =
	match args with
	| [] -> ()
	| lst::[] -> let str_arg = to_string lst in
		output_string oc str_arg
	| hd::tl ->  let str_arg = to_string hd in
		output_string oc str_arg; output_string oc delim; flush oc;
		print_list ~delim:delim ~oc:oc to_string tl

let print_list_endline ?oc:(oc=stdout) to_string args =
	if (args=[]) then ()
	else (print_list ~delim:"\n" ~oc:oc to_string args; output_char oc '\n';)

let is_loop_closing_block bb_uid insn =
	List.mem bb_uid insn.Fnc.loop_closing_targets

let is_void op =
	match op.Operand.data with
	| OpVoid -> true
	| _ -> false

let is_ptr op =
	let typ = get_type op.Operand.typ in
	match typ.code with
	| TypePtr _ -> true
	| _ -> false

let is_constant op =
	match op.Operand.data with
	| OpCst _ -> true
	| _ -> false

let is_extern op =
	match op.Operand.data with
	| OpCst { cst_data } -> ( match cst_data with
		| CstFnc fnc -> fnc.is_extern
		| _ -> false )
	| _ -> false

let is_fnc_static f =
	let scope = f.Fnc.def.scope in
		scope == CL_SCOPE_STATIC

let is_fnc_nonreturn f =
	let typ = get_type f.Fnc.def.typ in
	match typ.code with
	| TypeFnc t ->
		let return_type = get_type ((Array.get t 0).item_typ) in
		if return_type.size=0 then true else false
	| _ -> false

let get_fnc_uid_from_op op =
	match op.Operand.data with
	| OpCst { cst_data } -> ( match cst_data with
		| CstFnc fnc -> fnc.uid
		| _ -> assert false )
	| _ -> assert false

let get_fnc_uid f = get_fnc_uid_from_op f.Fnc.def

let get_fnc_loc_from_op op =
	match op.Operand.data with
	| OpCst { cst_data } -> ( match cst_data with
		| CstFnc fnc -> fnc.loc
		| _ -> assert false )
	| _ -> assert false

let get_fnc_loc f = get_fnc_loc_from_op f.Fnc.def

let get_fnc_vars uid =
	match (get_fnc_opt uid) with
	| None -> []
	| Some f -> f.vars

let get_fnc_args uid =
	let f = get_fnc uid in
	f.args

let get_used_gvars_for_fnc uid =
	let fvars = get_fnc_vars uid in
	list_inter fvars stor.global_vars

let get_anchors uid =
	let f = get_fnc uid in
	f.args @ (get_used_gvars_for_fnc uid)

let get_anchors_uid uid =
	List.map (fun elm -> (-elm)) (get_anchors uid)

let get_pvars uid =
	0::(get_anchors_uid uid) @
	(list_join_unique (get_fnc_vars uid) stor.global_vars)

let get_pvars_for_fnc uid =
	0::(get_anchors_uid uid) @ (get_fnc_vars uid)

let find_block uid fnc = List.assoc_opt uid fnc.Fnc.cfg

let get_var_uid_from_op op =
	match op.Operand.data with
	| OpVar uid -> uid
	| _ -> assert false

let rec check_fncs uid fncs =
	match fncs with
	| [] -> assert false
	| (_,f)::tl -> let bb = find_block uid f in (match bb with
		| None -> check_fncs uid tl
		| Some bb -> bb
	)

let get_insns_from_block uid =
	let bb = check_fncs uid stor.Storage.fncs in bb.insns

let get_block uid = (uid, (check_fncs uid stor.Storage.fncs))

let get_block_loc uid =
	let insns = get_insns_from_block uid in
	let fst = List.hd insns in
	fst.loc

let get_type_code uid =
	let typ = get_type uid in
	typ.code

let get_type_size uid =
	let typ = get_type uid in
	typ.size

let get_type_ptr uid =
	let typ = get_type uid in
	match typ.code with
	| TypePtr t -> t
	| _ -> assert false

let get_type_array uid =
	let typ = get_type uid in
	match typ.code with
	| TypeArray (_, t) -> t
	| _ -> assert false

let get_type_item items id =
	let i = Array.get items id in
	let iname = (match i.item_name with
		| Some x -> x
		| None -> "<anon_item>") in
	(iname, i.item_offset, i.item_typ)

let get_accessor_item ac =
	match ac.acc_data with
	| Item id -> let actype = get_type ac.acc_typ in
		(match actype.code with
		| TypeStruct elms | TypeUnion elms -> get_type_item elms id
		| _ -> assert false)
	| _ -> assert false

let get_NOP () = { Fnc.code=InsnNOP; loc=None; loop_closing_targets=[] }

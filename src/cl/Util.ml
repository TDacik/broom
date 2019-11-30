(* Useful functions for Code Listener Storage *)

(* newer lib: Atdgen_runtime.Util *)
module AGU = Ag_util

open Type
open Operand

let error loc msg = Printf.eprintf "%s error: %s\n" loc msg

(* TODO: only if develop mode *)
let internal_error loc msg = failwith (loc ^ " " ^ msg)


(* FIXME: read-only global variable? *)
let stor = AGU.Json.from_channel Storage.read_t stdin

let get_fnc uid = List.assoc uid stor.Storage.fncs

let get_type uid = List.assoc uid stor.Storage.types

let get_var uid = List.assoc uid stor.Storage.vars

let is_void op =
	match op.Operand.data with
	| OpVoid -> true
	| _ -> false

let is_fnc_static f =
	let scope = f.Fnc.def.scope in
		scope == CL_SCOPE_STATIC

let get_type_item items id =
	let i = Array.get items id in
	let iname = (match i.item_name with
		| Some x -> x
		| None -> "<anon_item>") in
	(iname, i.item_offset)

let get_accessor_item ac =
	match ac.acc_data with
	| Item id -> let actype = get_type ac.acc_typ in
		(match actype.code with
		| TypeStruct elms | TypeUnion elms -> get_type_item elms id
		| _ -> assert false)
	| _ -> assert false

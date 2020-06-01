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

let rec list_to_string to_string args =
	match args with
	| [] -> ""
	| lst::[] -> to_string lst
	| hd::tl -> (to_string hd) ^ ", " ^ (list_to_string to_string tl)

(* Print list of elms separated by ',' calling 'to_string' on each elm *)
let rec print_list to_string args =
	match args with
	| [] -> ()
	| lst::[] -> let str_arg = to_string lst in
		Printf.printf "%s" str_arg
	| hd::tl ->  let str_arg = to_string hd in
		Printf.printf "%s, " str_arg;
		print_list to_string tl

let is_void op =
	match op.Operand.data with
	| OpVoid -> true
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

let find_block uid fnc = List.assoc_opt uid fnc.Fnc.cfg

let rec check_fncs uid fncs =
	match fncs with
	| [] -> assert false
	| (_,f)::tl -> let bb = find_block uid f in (match bb with
		| None -> check_fncs uid tl
		| Some bb -> bb
	)

let get_insns_from_block uid = let bb = check_fncs uid stor.Storage.fncs in bb.insns

let get_block uid = (uid, (check_fncs uid stor.Storage.fncs))

let get_type_size uid =
	let typ = get_type uid in
	typ.size

let get_type_ptr uid =
	let typ = get_type uid in
	match typ.code with
	| TypePtr t -> t
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

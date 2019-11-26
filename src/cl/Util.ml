(* Useful functions for Code Listener Storage *)

(* newer lib: Atdgen_runtime.Util *)
module AGU = Ag_util

type uid = int

(* read-only global variable? *)
let stor = AGU.Json.from_channel Storage.read_t stdin

(* Get function from association list in storage *)
let get_fnc uid = List.assoc uid stor.Storage.fncs

(* Get type info from association list in storage *)
let get_type uid = List.assoc uid stor.Storage.types

(* Get variable from association list in storage *)
let get_var uid = List.assoc uid stor.Storage.vars

let is_void op =
	match op.Operand.data with
	| OpVoid -> true
	| _ -> false

let is_fnc_static f =
	let scope = f.Fnc.def.scope in
		scope == CL_SCOPE_STATIC

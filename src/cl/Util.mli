(** Interface for useful functions for Code Listener Storage and error output *)

(** [error loc msg] *)
val error: string -> string -> unit

(** [internal_error loc msg] *)
val internal_error: string -> string -> 'a


val stor : Storage.t

(** [get_fnc uid] gets function from association list in storage *)
val get_fnc: Loc.cl_uid -> Fnc.t

(** [get_type uid] gets type info from association list in storage *)
val get_type: Loc.cl_uid -> Type.t

(** [get_var uid] gets variable from association list in storage *)
val get_var: Loc.cl_uid -> Var.t

(** [is_viod op] if operand is void *)
val is_void: Operand.t -> bool

val is_fnc_static: Fnc.t -> bool

(** [get_type_item items id] gets (name, offset) of type item on index [id] -
	for structured types only *)
val get_type_item: Type.cl_type_item array -> int -> (string * int)

(** [get_accessor_item acc] *)
val get_accessor_item : Operand.cl_accessor -> (string * int)

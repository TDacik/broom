(** Interface for useful functions for Code Listener Storage *)

type uid = int

val stor : Storage.t

(** [get_fnc uid] gets function from association list in storage *)
val get_fnc: uid -> Fnc.t

(** [get_type uid] gets type info from association list in storage *)
val get_type: uid -> Type.t

(** [get_var uid] gets variable from association list in storage *)
val get_var: uid -> Var.t

(** [is_viod op] if operand is void *)
val is_void: Operand.t -> bool

val is_fnc_static: Fnc.t -> bool

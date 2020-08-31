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

val get_var_opt: Loc.cl_uid -> Var.t option

(** [list_diff list1 list2] gets difference between two lists;
    list as a homogeneous set *)
val list_diff: 'a list -> 'a list -> 'a list

(** [list_inter list1 list2] gets intersection of two lists;
    list as a homogeneous set *)
val list_inter: 'a list -> 'a list -> 'a list

(** [list_max_positive l] finds max positive number in list *)
val list_max_positive: int list -> int

(** [list_join_unique l1 l2] adds missing elements of list [l1] to [l2] *)
val list_join_unique: 'a list -> 'a list -> 'a list

(** [list_to_string to_string args] gets string of elms separated by ',' calling
	[to_string] on each elm *)
val list_to_string: ('a -> string) -> 'a list -> string

(** [print_list to_string args] prints list of elms separated by ',' calling
	[to_string] on each elm *)
val print_list: ('a -> string) -> 'a list -> unit

(** [is_loop_closing_block bb_uid insn] *)
val is_loop_closing_block: Loc.cl_uid -> Fnc.insn -> bool

(** [is_viod op] if operand is void *)
val is_void: Operand.t -> bool

(** [is_extern op] if operand is extern - valid for function *)
val is_extern: Operand.t -> bool

val is_fnc_static: Fnc.t -> bool

val get_fnc_uid_from_op: Operand.t -> Loc.cl_uid

val get_fnc_uid: Fnc.t -> Loc.cl_uid

(** [get_fnc_vars uid] gets uids of varables used in function given by uid *)
val get_fnc_vars: Loc.cl_uid -> Loc.cl_uid list

(** [get_fnc_vars uid] gets uids of arguments used in function given by uid *)
val get_fnc_args: Loc.cl_uid -> Loc.cl_uid list

(** [get_anchors_uid uid] *)
val get_anchors_uid: Loc.cl_uid -> int list

(** [get_pvars uid] gets uids of program variables used in function (include
    all global variables) given by uid, anchors for arguments and variable
    for return of function *)
val get_pvars: Loc.cl_uid -> int list

(** [get_pvars_for_fnc uid] gets uids of program variables used in function
    (include global variables) given by uid, anchors for arguments and variable
    for return of function *)
val get_pvars_for_fnc: Loc.cl_uid -> int list

(** [get_insns_from_block uid] *)
val get_insns_from_block: Loc.cl_uid -> Fnc.insn list

val get_block: Loc.cl_uid -> (Loc.cl_uid * Fnc.block)

val get_type_size : Loc.cl_uid -> int

val get_type_ptr : Loc.cl_uid -> Loc.cl_uid

(** [get_type_item items id] gets (name, offset, typ) of type item on index
	[id] - for structured types only *)
val get_type_item: Type.cl_type_item array -> int -> (string * int * Loc.cl_uid)

(** [get_accessor_item acc] *)
val get_accessor_item : Operand.cl_accessor -> (string * int * Loc.cl_uid)

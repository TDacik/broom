(** Interface of Pretty printer for Code Listener Storage *)

(** [loc_to_string loc] gets CL code location as string *)
val loc_to_string: Loc.t option -> string

(** [type_to_string uid] gets CL type as string *)
val type_to_string: Loc.cl_uid -> string

(** [var_to_string uid] gets CL operand as string *)
val var_to_string: Loc.cl_uid -> string

(** [operand_to_string op] gets CL operand as string *)
val operand_to_string: Operand.t -> string

(** [print_insn insn] prints CL instruction *)
val print_insn: Fnc.insn -> unit

(** [print_block apply_on_insn bb] prints basic block of function and applies
	'apply_on_insn' on each instruction *)
val print_block: (Fnc.insn -> unit) -> Loc.cl_uid * Fnc.block -> unit

val get_fnc_name: Fnc.t -> string

val print_fnc_declaration : Fnc.t -> unit

val print_cfg : (Fnc.insn -> unit) -> (Loc.cl_uid * Fnc.block) list -> unit

(** [print_fnc ?apply_on_insn (uid,f)] prints function and applies
	'apply_on_insn' on each instruction *)
val print_fnc: ?apply_on_insn:(Fnc.insn -> unit) -> (Loc.cl_uid * Fnc.t) -> unit

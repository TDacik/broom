(** Interface of Pretty printer for Code Listener Storage *)

type uid = int

(** [loc_to_string loc] gets CL code location as string *)
val loc_to_string: Loc.t -> string

(** [type_to_string uid] gets CL type as string *)
val type_to_string: uid -> string

(** [var_to_string uid] gets CL operand as string *)
val var_to_string: uid -> string

(** [operand_to_string op] gets CL operand as string *)
val operand_to_string: Operand.t -> string

(** [print_list to_string args] prints list of elms separated by ',' calling
	[to_string] on each elm *)
val print_list: ('a -> string) -> 'a list -> unit

(** [print_insn insn] prints CL instruction *)
val print_insn: Fnc.insn -> unit

(** [print_block apply_on_insn bb] prints basic block of function and applies
	'apply_on_insn' on each instruction *)
val print_block: (Fnc.insn -> unit) -> Fnc.block -> unit

(** [print_fnc ?apply_on_insn (uid,f)] prints function and applies
	'apply_on_insn' on each instruction *)
val print_fnc: ?apply_on_insn:(Fnc.insn -> unit) -> (uid * Fnc.t) -> unit

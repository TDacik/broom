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

(** Interface of Pretty printer for Code Listener Storage *)

(** [type_to_string uid] gets CL type as string *)
val type_to_string: Loc.cl_uid -> string

(** [var_to_string uid] gets CL operand as string *)
val var_to_string: Loc.cl_uid -> string

(** [operand_to_string op] gets CL operand as string *)
val operand_to_string: Operand.t -> string

val get_fnc_name: Fnc.t -> string

val fnc_declaration_to_string: Fnc.t -> string

(** [insn_to_string ?indent insn] gets CL instruction as string; if indend is
    true, instructions are indented by 2 tabs *)
val insn_to_string: ?indent:bool -> Fnc.insn -> string

(** {3 Printing on stdard output} *)

(** [print_insn insn] prints CL instruction *)
val print_insn: Fnc.insn -> unit

(** [prerr_insn insn] prints CL instruction on stderr *)
val prerr_insn: Fnc.insn -> unit

(** [print_block apply_on_insn bb] prints basic block of function and applies
	'apply_on_insn' on each instruction *)
val print_block: (Fnc.insn -> unit) -> Loc.cl_uid * Fnc.block -> unit

val print_cfg : (Fnc.insn -> unit) -> (Loc.cl_uid * Fnc.block) list -> unit

(** [print_fnc ?apply_on_insn (uid,f)] prints function and applies
	'apply_on_insn' on each instruction *)
val print_fnc: ?apply_on_insn:(Fnc.insn -> unit) -> (Loc.cl_uid * Fnc.t) -> unit

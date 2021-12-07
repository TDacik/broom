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

(** Interface for useful functions for Code Listener Storage *)

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

(** [print_list ~delim:delim ~oc:oc to_string args] prints list of elms
    separated by [delim] (default ', ') [to_string] on each elm to the output
    defined by [oc] (default stdout) *)
val print_list: ?delim:string -> ?oc:out_channel -> ('a -> string) -> 'a list
                -> unit

(** [print_list ~oc:oc to_string args] prints list of elms on new line, calling
    [to_string] on each elm; prints to the output defined by [oc] (default
    stdout) *)
val print_list_endline: ?oc:out_channel -> ('a -> string) -> 'a list -> unit

(** [is_loop_closing_block bb_uid insn] *)
val is_loop_closing_block: Loc.cl_uid -> Fnc.insn -> bool

(** [is_viod op] if operand is void *)
val is_void: Operand.t -> bool

(** [is_ptr op] if operand's type is pointer *)
val is_ptr: Operand.t -> bool

val is_constant: Operand.t -> bool

(** [is_extern op] if operand is extern - valid for function *)
val is_extern: Operand.t -> bool

val is_fnc_static: Fnc.t -> bool

val is_fnc_nonreturn: Fnc.t -> bool

val get_fnc_uid_from_op: Operand.t -> Loc.cl_uid

val get_fnc_uid: Fnc.t -> Loc.cl_uid

val get_fnc_loc: Fnc.t -> Loc.t option

(** [get_fnc_vars uid] gets uids of varables used in function given by uid *)
val get_fnc_vars: Loc.cl_uid -> Loc.cl_uid list

(** [get_fnc_vars uid] gets uids of arguments used in function given by uid *)
val get_fnc_args: Loc.cl_uid -> Loc.cl_uid list

(** [get_used_gvars_for_fnc uid] *)
val get_used_gvars_for_fnc: Loc.cl_uid -> Loc.cl_uid list

(** [get_anchors uid] gets uids of arguments and global variables used in
    function given by uid *)
val get_anchors: Loc.cl_uid -> Loc.cl_uid list

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

val get_var_uid_from_op: Operand.t -> Loc.cl_uid

(** [get_insns_from_block uid] *)
val get_insns_from_block: Loc.cl_uid -> Fnc.insn list

val get_block: Loc.cl_uid -> (Loc.cl_uid * Fnc.block)

val get_type_code : Loc.cl_uid -> Type.cl_type_e

val get_type_size : Loc.cl_uid -> int

val get_type_ptr : Loc.cl_uid -> Loc.cl_uid

val get_type_array : Loc.cl_uid -> Loc.cl_uid

(** [get_type_item items id] gets (name, offset, typ) of type item on index
	[id] - for structured types only *)
val get_type_item: Type.cl_type_item array -> int -> (string * int * Loc.cl_uid)

(** [get_accessor_item acc] *)
val get_accessor_item : Operand.cl_accessor -> (string * int * Loc.cl_uid)

(** [get_NOP] returns empty instruction *)
val get_NOP : unit -> Fnc.insn

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

module Exp : sig
  type t =
        Var of variable
          (** - lvars - existential local variables in the scope of a function
              - 0 - spetial case for return
			  - uid<0 - spetial cases for anchors of function
              - pvars - program variables, unique in the scope of a file *)
      | CVar of int
      | Const of const_val
      (* todo | Interval... *)
      | UnOp of unop * t
      | BinOp of binop * t * t
      | Void
      | Undef

    and unop =
        Base
      | Len
      | Stack    (** stack allocation *)
      | Static   (** static storage *)
      | Freed    (** for heap allocation *)
      | Invalid  (** for stack allocation *)
      | BVnot    (** bitwise, in C: ~ *)
      | Pnot     (** logical, in C: ! *)
      | Puminus  (** in C: - *)

    (* aritmetic operation *)
    and binop =
        Peq      (** equality *)
      | Pneq     (** nonequality *)
      | Pless    (** less then *)
      | Plesseq  (** less or equal then *)
      | Pand     (** logical AND *)
      | Por      (** logical OR *)
      | Pxor     (** logical XOR *)
      | Pplus
      | Pminus   (** for pointers - in same alloc block *)
      | Pmult
      | Pdiv     (** CL_BINOP_EXACT_DIV: for pointers - div without rounding *)
      | Pmod
      | BVand    (** bitwise AND *)
      | BVor     (** bitwise OR *)
      | BVxor    (** bitwise XOR *)
      | BVlshift
      | BVrshift (** logical on unsigned, arithmetic on signed *)
      | BVlrotate
      | BVrrotate


    and const_val =
        Ptr of int
      | Int of Int64.t
      | Bool of bool
      | String of string
      | Float of float

    and variable = int

  val one : t
  val zero : t
  val null : t
  val ret : t
  val variable_to_string : ?lvars:variable list -> variable -> string
  val cvariable_to_string : int -> string
  val const_to_string : const_val -> string
  val unop_to_string : unop -> string
  val binop_to_string : binop -> string
  val to_string : ?lvars:variable list -> t -> string

  (** [get_list_vars uids] gets list of Var expressions from list of uids *)
  val get_list_vars: variable list -> t list

  (** [get_list_uids vars] gets list of uids from list of Var expressions *)
  val get_list_uids: t list -> variable list
end

exception ErrorInFormula of (string * Config.src_pos)

type t = {
    sigma: sigma;  (** spatial part *)
    pi: pi;  (** pure part *)
}

and pi = Exp.t list

and lambda = {
  param: Exp.variable list;
  form: t;
}

and heap_pred =
  | Hpointsto of Exp.t * Exp.t * Exp.t (** source, size_of_field, destination *)
  | Slseg of Exp.t * Exp.t * lambda * Exp.t list    (** source, destination, lambda, shared *)
  (* first, backlink from first, last, forwardlink from last, lambda, shared *)
  | Dlseg of Exp.t * Exp.t * Exp.t * Exp.t * lambda * Exp.t list

and sigma = heap_pred list

val empty : t

val lvariables_to_string : Exp.variable list -> string

val points_to_to_string: ?lvars:Exp.variable list -> heap_pred -> string

val to_string : ?lvars:Exp.variable list -> t -> string

val print : ?lvars:Exp.variable list -> t -> unit

val print_with_lambda : ?lvars:Exp.variable list -> t -> unit

(** [diff f1 f2] *)
val diff : t -> t -> t

(** [disjoint_union f1 f2] *)
val disjoint_union : t -> t -> t

(** [is_invalid pi] returns true, if [pi] contains Invalid predicate *)
val is_invalid : pi -> bool

(** [is_abstract f] returns true, if [f.sigma] contains abstract predicates *)
val is_abstract : t -> bool

(** {3 Find all variables in formula} *)

(** [find_and_remove_var_pointsto obj sigma cvars] returns variable pointed to
    object [obj] and new sigma without points-to otherwise fresh cvar and sigma
*)
val find_and_remove_var_pointsto : Exp.t -> sigma -> int ->
                                   (Exp.t * sigma * int)

(** [find_vars_expr expr] *)
val find_vars_expr : Exp.t -> Exp.variable list

(** [find_vars form] provides a list of all variables used in the formula [form]
    expect contract variables *)
val find_vars : t -> Exp.variable list


(** {3 Formula simplification} *)

(** [subformula_only vars form] returns list of all variables in subformula
    including vars and a subformula that contains only clauses with variables
    from [vars] *)
val subformula_only : Exp.t list -> t -> (Exp.t list * t)

(** [var_is_reachable f var vars] returns true, if [var] depends on at least
    one vraiable from [vars] in formula [f] *)
val var_is_reachable : t -> Exp.variable -> Exp.variable list -> bool

(** [get_equiv_vars a pi] get all variables equivalent with [a] from pure part
    by computing a transitive closure *)
val get_equiv_vars : Exp.variable list -> pi -> Exp.variable list


(** [substitute_expr new_expr old_expr expr] *)
val substitute_expr : Exp.t -> Exp.t -> Exp.t -> Exp.t

(** [substitute_vars new_var old_var form] *)
val substitute_vars : Exp.variable -> Exp.variable -> t -> t

(** [substitute_vars_cvars new_var old_var form] same as above, but vars should be Var/CVar *)
val substitute_vars_cvars : Exp.t -> Exp.t -> t -> t

(** [substitute_expr_all new_vars old_vars form] substitutes
    [List.nth i old_vars] by [List.nth i new_vars] in [form], therefore
    [List.length old_vars = List.length new_vars] must hold
    @raise ErrorInFromula if [new_vars] and [old_vars] have unequal length
*)
val substitute_expr_all : Exp.t list -> Exp.t list -> t -> t

(** [substitute var eqvarlist form] *)
val substitute : Exp.variable -> Exp.variable list -> t -> t

(** [remove_redundant_eq pi] removes redundant equalities from pure part
    formula *)
val remove_redundant_eq : pi -> pi

(** [remove_equiv_vars gvars evars form] renames equivalent variables as one,
    where [gvars] are global variables and [evars] are existential
    variables *)
val remove_equiv_vars : Exp.variable list -> Exp.variable list -> t -> t

(** [remove_useless_conjuncts form evars exclude_from_refs] removes usless
    conjuncts from pure part of [form] - a conjunct is useless iff
      + contains vars only from [evars] only
      + there is no transitive reference from spatial part or program variables

    [form] expect satisfiable formula only 
    [exclude_from_refs] is a set of variables, which are considered not
    referenced by sigma *)
val remove_useless_conjuncts : t -> Exp.variable list -> Exp.variable list -> t

(** [simplify form evars] is global simplify function, [evars] is a list of Ex.
    q. variables, which can be renamed/removed/etc...
    [form] - expect satisfiable formula only *)
val simplify : t -> Exp.variable list -> t

(** [simplify_lambda form evars lambda_refs] this is used in the lambda
    creation.
    - Everything related only to the referenced variables (lambda_refs) is
      removed from pi.
    - lambda_refs can not be removed (resp. renamed) from sigma *)
val simplify_lambda : t -> Exp.variable list -> Exp.variable list -> t

(** {3 Rename conflicting logical variables} *)

(** [rename_ex_variables form evars conflicts] creates fresh names for evars
    with conflicts *)
val rename_ex_variables : t -> Exp.variable list -> Exp.variable list -> t * Exp.variable list


(** {3 Unfold predicate} *)

val unfold_predicate : t -> int -> Exp.variable list -> int -> t * Exp.variable list
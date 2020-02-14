module Exp : sig
  type t =
      | Var of variable
      | CVar of int
      | Const of const_val
      (* todo | Interval... *)
      | UnOp of unop * t
      | BinOp of binop * t * t
      | Void
      | Undef

    and unop =  Base | Len | Freed

    (** aritmetic operation *)
    and binop =
      | Peq    (** equality *)
      | Pneq   (** nonequality *)
      | Pless  (** less then *)
      | Plesseq (** less or equal then **)
      | Pplus
      | Pminus (** in same alloc block *)

    and const_val =
        Ptr of int
      | Int of Int64.t
      | Bool of bool
      | String of string
      | Float of float

    and variable = int

  val variable_to_string : variable -> string
  val const_to_string : const_val -> string
  val unop_to_string : unop -> string
  val binop_to_string : binop -> string
  val to_string : t -> string
end


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
  | Slseg of Exp.t * Exp.t * lambda    (** source, destination, lambda *)

and sigma = heap_pred list

val empty : t

val lvariables_to_string : Exp.variable list -> string

val to_string : t -> string

val print : t -> unit

(** {3 Find all variables in formula} *)

(** [join_list_unique l1 l2] adds missing elements of list [l1] to [l2] *)
val join_list_unique : 'a list -> 'a list -> 'a list

(** [find_vars form] provides a list of all variables used in the formula form *)
val find_vars : t -> Exp.variable list

(** {3 Formula simplification} *)

(** [remove_redundant_eq pi] removes redundant equalities from pure part
    formula *)
val remove_redundant_eq : pi -> pi

val remove_unused_evars : t -> Exp.variable list -> Exp.variable list

(** [simplify_ll gvars evars form] simplify the formula, where [gvars] are
    global variables and [evars] are existential variables *)
val simplify_ll : Exp.variable list -> Exp.variable list -> t -> t

(** [simplify form evars] is global simplify function, [evars] is a list of Ex.
    q. variables, which can be renamed/removed/etc...*)
val simplify : t -> Exp.variable list -> t

(** {3 Rename conflicting logical variables} *)

(** [rename_ex_variables form evars conflicts] creates fresh names for evars
    with conflicts *)
val rename_ex_variables : t -> Exp.variable list -> Exp.variable list -> t * Exp.variable list

(** {3 Unfold predicate} *)

val unfold_predicate : t -> int -> Exp.variable list -> t * Exp.variable list





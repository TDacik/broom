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
  val cvariable_to_string : int -> string
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

val print_with_lambda : t -> unit

(** {3 Find all variables in formula} *)

(** [join_list_unique l1 l2] adds missing elements of list [l1] to [l2] *)
val join_list_unique : 'a list -> 'a list -> 'a list

(** [find_var_pointsto obj sigma cvars] returns variable pointed to object [obj] otherwise fresh cvar *)
val find_var_pointsto : Exp.t -> sigma -> int -> (Exp.t * int)

(** [find_vars_expr expr] *)
val find_vars_expr : Exp.t -> Exp.variable list

(** [find_vars form] provides a list of all variables used in the formula form
    expect contract variables *)
val find_vars : t -> Exp.variable list


(** {3 Formula simplification} *)

(** [get_varmap f] simplify formula by removing equivalent existential variables
    get a list of pair of equal variables from Pure part *)
val get_varmap : pi -> (Exp.variable * Exp.variable) list

(** [get_eq_vars varlist equalities] computes a transitive closure *)
val get_eq_vars : 'a list -> ('a * 'a) list -> 'a list

(** [substitute_vars new_var old_var form] *)
val substitute_vars : Exp.variable -> Exp.variable -> t -> t

(** [substitute_vars_cvars new_var old_var form] same as above, but vars should be Var/CVar *)
val substitute_vars_cvars : Exp.t -> Exp.t -> t -> t

(** [substitute var eqvarlist form] *)
val substitute : Exp.variable -> Exp.variable list -> t -> t

(** [remove_redundant_eq pi] removes redundant equalities from pure part
    formula *)
val remove_redundant_eq : pi -> pi

val remove_useless_conjuncts : t -> Exp.variable list -> t

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

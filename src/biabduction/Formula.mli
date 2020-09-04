module Exp : sig
  type t =
        Var of variable (** lvars - existential local variables in the scope of
                                    a function
                                  - spetial cases: var 0 - return, var uid<0
                                    arguments
                            pvars - program variables, unique in the scope of
                                    a file *)
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
      | Freed
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

val to_string : ?lvars:Exp.variable list -> t -> string

val print : ?lvars:Exp.variable list -> t -> unit

val print_with_lambda : ?lvars:Exp.variable list -> t -> unit

(** [diff f1 f2] *)
val diff : t -> t -> t

(** [disjoint_union f1 f2] *)
val disjoint_union : t -> t -> t


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

(** [subformula vars form] returns
    flag if something was removed from spatial part
    list of all variables that may be in subformula
    a subformula that contains clauses with variables from [vars] and related
    variables to them
    [form] - expect satisfiable formula only
    [vars] - list of Exp, but expect CVar and Var only *)
val subformula : Exp.t list -> t -> bool * Exp.t list * t

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

(** [remove_equiv_vars gvars evars form] renames equivalent variables as one,
    where [gvars] are global variables and [evars] are existential
    variables *)
val remove_equiv_vars : Exp.variable list -> Exp.variable list -> t -> t

(** [remove_useless_conjuncts form evars] removes usless conjuncts from pure
    part of [form] - a conjunct is useless iff
      1a) contains vars only from [evars] only
      1b) it is of the form exp1 != exp2 and evars are not togather with
          referenced ars in exp1/2
          i.e. r1 != e1 (r1 referenced, e1 existential) => not needed FIXME!
      2) there is no transitive reference from spatial part or program variables
    [form] expect satisfiable formula only *)
val remove_useless_conjuncts : t -> Exp.variable list -> t

(** [simplify2 fixed_vars form] is global simplify function, returns true, if
    something was removed from sigma and simplified formula
    [fixed_vars] - variables can't be removed
    [form] - expect satisfiable formula only *)
val simplify2 : Exp.variable list -> t -> bool * t

(** [simplify form evars] is global simplify function, [evars] is a list of Ex.
    q. variables, which can be renamed/removed/etc...
    [form] - expect satisfiable formula only *)
val simplify : t -> Exp.variable list -> t


(** {3 Rename conflicting logical variables} *)

(** [rename_ex_variables form evars conflicts] creates fresh names for evars
    with conflicts *)
val rename_ex_variables : t -> Exp.variable list -> Exp.variable list -> t * Exp.variable list


(** {3 Unfold predicate} *)

val unfold_predicate : t -> int -> Exp.variable list -> t * Exp.variable list

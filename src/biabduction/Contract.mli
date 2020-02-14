(* module FExp = Formula.Exp *)
open Formula

type formula = Formula.t
type variable = Exp.variable

type t = {
    lhs: formula;
    rhs: formula;
    cvars: int; (* variable list;*)
	(** list of contract variables -- local within the contract *)
    pvarmap: (variable * variable) list;
    (** the program variables may move to new positions.
        The pvarmap link program variables with contract variables representing
        the new positions; (old,new) *)
}

val to_string : t -> string

val print : t -> unit

val get_contract : CL.Fnc.insn -> t list

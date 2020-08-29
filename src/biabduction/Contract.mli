(* module FExp = Formula.Exp *)
open Formula

type formula = Formula.t
type variable = Exp.variable

type t = {
    lhs: formula;
    rhs: formula;
    cvars: int;
    (** number of contract variables count from 1 -- local within
        the contract *)
    pvarmap: (variable * variable) list;
    (** the program variables may move to new positions.
        The pvarmap link program variables with contract variables representing
        the new positions; (old,new) *)
}

val empty : t

val to_string : t -> string

val print : t -> unit

(* [subcontract vars c] contains in lhs and rhs only clauses with variables
   from vars and related variables
   if removes cvars, doesn't reduce count of contract variables
   vars - list of Exp, but expect CVar and Var only *)
(* FIXME vars should contain Xs from moves (_->X) *)
(* FIXME removing spatial part ignored *)
(* Don't use this function, use substate if possible ! *)
val subcontract : Exp.t list -> t -> t

(** [contract_for_called_fnc dst args num_args c] renames dst and args in given
    contract c; renaming from RET(c0) and args(c-1...) *)
val contract_for_called_fnc : CL.Operand.t -> CL.Operand.t list ->
                              int -> t -> t

val get_contract : CL.Fnc.insn -> t list

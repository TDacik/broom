(* module FExp = Formula.Exp *)
open Formula

type formula = Formula.t
type variable = Exp.variable

exception ErrorInContract of (string * Config.src_pos)

type status = OK | Error | Aborted | Unfinished (* | Unreached *)

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
    s: status;
}

val empty : t

(** [rw_rhs c] rewrites rhs with lhs and removes lhs *)
val rw_rhs : t -> t

(** [to_string not_unfinished c ] ctreates string representing contract c; if not_unfinished is true,
    unfinished contract isn't printed *)
val to_string : ?not_unfinished:bool -> t -> string

val print : t -> unit

val is_OK : t -> bool

(** [get_storage ptr var] returns size of storage and pure part desribed
    storage of [var]
    arguments are Exp.t but only Var/CVar *)
val get_storage_with_size : Exp.t -> Exp.t -> (Exp.t * pi)

(* [subcontract vars c] contains in lhs and rhs only clauses with variables
   from vars and related variables
   if removes cvars, doesn't reduce count of contract variables
   vars - list of Exp, but expect CVar and Var only *)
(* FIXME not removes false predicates *)
(* FIXME vars should contain Xs from moves (_->X) *)
(* FIXME removing spatial part ignored *)
(* Don't use this function, use substate if possible ! *)
(* val subcontract : Exp.t list -> t -> t *)

(** [contract_for_called_fnc dst args fuid c] renames dst and args in given
    contract c for function fuid; renaming from RET(c0) and anchors(uid<0)
    @raise Assert_failure if formula for [args] could semantically overlap with
    lhs of c *)
val contract_for_called_fnc : CL.Operand.t -> CL.Operand.t list ->
                              CL.Loc.cl_uid -> t -> t

val contract_for_unfinished_fnc : CL.Fnc.t -> t

val get_contract : CL.Fnc.insn -> t list

module FExp = Formula.Exp

(** Raise in case of ... *)
exception Conflict_between_freed_and_slseg

(** Raise in case of ... *)
exception RemovedSpatialPartFromMiss

(** [remove_freed_and_invalid_parts solver form] returns formula without
    spetial parts related to freed (on heap) and invalid (on stack) predicates
*)
val remove_freed_and_invalid_parts : Z3wrapper.solver -> Formula.t -> Formula.t

(** [remove_stack ?(replaced=false) solver form] returns formula without
    spatial parts on stack and related stack predicates; if [replaced] is true,
    stack predicates are replaced with invalid predicates *)
val remove_stack : ?replaced:bool -> Z3wrapper.solver -> Formula.t -> Formula.t

(** [remove_stack2 ?(replaced=false) solver form lvars] does same as
    remove_stack expect only for non-program variables [lvars]; because
    abduction doing something weird, when is used only remove_stack *)
val remove_stack2 : ?replaced:bool -> Z3wrapper.solver -> Formula.t ->
                    FExp.variable list -> Formula.t

(** [subformula solver vars form] returns
    flag if something was removed from spatial part
    list of all variables that may be in subformula
    a subformula that contains clauses with variables from [vars] and related
    variables to them
    [form] - expect satisfiable formula only
    [vars] - list of Exp, but expect CVar and Var only *)
val subformula : Z3wrapper.solver -> FExp.t list -> Formula.t ->
                 bool * FExp.t list * Formula.t

(** [substate solver fixed_vars state] contains in miss and curr only clauses
    with variables from [fixed_vars] and related variables
    [state] - expect satisfiable state only
    [fixed_vars] - list of Exp, but expect CVar and Var only *)
val substate : Z3wrapper.solver -> FExp.t list -> State.t -> State.t


(* SIMPLIFY *)

(** [formula solver fixed_vars form] is global simplify function for formula,
    returns true, if something was removed from sigma and simplified [form]
    [fixed_vars] - variables can't be removed
    [form] - expect satisfiable formula only *)
val formula : Z3wrapper.solver -> FExp.variable list -> Formula.t ->
              bool * Formula.t

(** [state solver fixed_vars state] simplifies state. If something left in
    spatial of miss not related to [fixed_vars], the RemovedSpatialPartFromMiss
    exception is raised. If something left in spatial part of curr, memory leak
    is reported.
    fixed_vars - variables can't be removed
    state - expect satisfiable state only *)
(* FIXME may be more variables in lvars than are in state *)
val state : Z3wrapper.solver -> FExp.variable list -> State.t -> State.t

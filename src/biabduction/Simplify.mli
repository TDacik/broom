module FExp = Formula.Exp

(** Raise in case of ... *)
exception Conflict_between_freed_and_lseg

(** Raise in case of ... *)
exception RemovedSpatialPartFromMiss

(** Raise in case of ... *)
exception RemovedSpatialPartFromCurr

(** [remove_freed_and_invalid_parts solver form] returns formula without
    spetial parts related to freed (on heap) and invalid (on stack) predicates
*)
val remove_freed_and_invalid_parts : Z3wrapper.solver -> Formula.t -> Formula.t

(** [remove_stack ?(replaced=false) solver form] returns formula without
    spatial parts on stack and related stack predicates; if [replaced] is true,
    stack predicates are replaced with invalid predicates *)
val remove_stack : ?replaced:bool -> Z3wrapper.solver -> Formula.t -> Formula.t

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
    state - expect satisfiable state only
    @raise RemovedSpatialPartFromMiss if part of spatial part in state.miss is
           not accesible by [fixed_vars] and related variables
    @raise RemovedSpatialPartFromCurr if part of spatial part in state.curr is
           not accesible by [fixed_vars] and related variables and if
           memory_leaks_as_errors is true *)
(* FIXME may be more variables in lvars than are in state *)
val state : Z3wrapper.solver -> FExp.variable list -> State.t -> State.t

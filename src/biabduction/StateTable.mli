type cl_uid = CL.Loc.cl_uid

(*
  key is a unique uid of basic block
  value is entailment counter and list of states (miss, act1), (miss, act2)...
*)

type st_value = {
    cnt: int; (** number of entailment calls *)
    states: State.t list
}

type st_tbl = (cl_uid, st_value) Hashtbl.t

type t = {
	fuid: cl_uid; (** for which function *)
	mutable fst_run: bool;
	mutable rerun: Contract.t list; (** contracts that need to be rerun *)
	tbl: st_tbl
}

exception EntailmentLimit

val create : cl_uid -> t

(** [add tbl uid states] returns subset of [states] not covered by previous
    runs, where [uid] is basic block at the beginning of which we add [states]
 *)
val add : t -> cl_uid -> State.t list -> State.t list

(** [add_rerun tbl contract] adds [contract] which needs to be rerun *)
val add_rerun : t -> Contract.t -> unit

val start_rerun : t -> Contract.t list

val reset : t -> unit

type cl_uid = CL.Loc.cl_uid

(*
  key is a unique uid of basic block
  value is list of states (miss, act1), (miss, act2)...
*)

type t = (cl_uid, State.t list) Hashtbl.t

val create : t

(** [entailment_check tbl uid states] returns subset of [states] not covered by
    previous runs, where [uid] is basic block at the beginning of which we add
    [states] *)
val entailment_check : t -> cl_uid -> State.t list -> State.t list

val reset : t -> unit

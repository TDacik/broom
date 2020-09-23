type cl_uid = CL.Loc.cl_uid

(*
  key is a unique uid of basic block
  value is list of states (miss, act1), (miss, act2)...
*)

type st_tbl = (cl_uid, State.t list) Hashtbl.t

type t = {
    fuid: cl_uid; (** for which function *)
    tbl: st_tbl
}

val create : cl_uid -> t

(** [add tbl uid states] returns subset of [states] not covered by previous
    runs, where [uid] is basic block at the beginning of which we add [states]
 *)
val add : t -> cl_uid -> State.t list -> State.t list

val reset : t -> unit

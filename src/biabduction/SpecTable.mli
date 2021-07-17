type cl_uid = CL.Loc.cl_uid

(* 
  key is a unique uid of function
  value is list of contracts (pre, post1), (pre, post2)
        // or (pre, [post1,post2])... ?
*)

type t = (cl_uid, Contract.t list) Hashtbl.t

val create : t

val add : t -> cl_uid -> Contract.t list -> unit

(** [only_add tbl uid contracts] removes all correct contracts and leave new
    [contracts] and not correct contracts for function defined by [uid] *)
val only_add : t -> cl_uid -> Contract.t list -> unit

val find_opt : t -> cl_uid -> Contract.t list option

val print : t -> unit

val reset : t -> unit

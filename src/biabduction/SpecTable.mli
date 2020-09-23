type cl_uid = CL.Loc.cl_uid

type status = OK | Error | Aborted (* | Unreached *)

(* 
  key is a unique uid of function
  value is list of contracts (pre, post1), (pre, post2)
        // or (pre, [post1,post2])... ?
*)

type t = (cl_uid, (Contract.t * status) list) Hashtbl.t

val create : t

val add : t -> cl_uid -> (Contract.t * status) list -> unit

val find_opt : t -> cl_uid -> (Contract.t * status) list option

val print : t -> unit

val reset : t -> unit

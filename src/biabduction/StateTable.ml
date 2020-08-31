type cl_uid = CL.Loc.cl_uid

(*
  key is a unique uid of basic block
  value is list of states (miss, act1), (miss, act2)...
*)

type t = (cl_uid, State.t list) Hashtbl.t

let create = let (bb_tbl : t) = Hashtbl.create 1 in bb_tbl

let add tbl uid states =
	let found = Hashtbl.find_opt tbl uid in
	match found with
	| None -> Hashtbl.add tbl uid states; states (* first entry *)
	| Some old_states -> Hashtbl.replace tbl uid (old_states @ states);states

let find_opt tbl x = Hashtbl.find_opt tbl x

let reset = Hashtbl.reset

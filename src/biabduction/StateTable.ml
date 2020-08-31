type cl_uid = CL.Loc.cl_uid

(*
  key is a unique uid of basic block
  value is list of states (miss, act1), (miss, act2)...
*)

type t = (cl_uid, State.t list) Hashtbl.t

let create = let (bb_tbl : t) = Hashtbl.create 1 in bb_tbl

(* entailment check form1 <= form2 *)
(* FIXME which evars for Abduction.entailment ? *)
let rec entailment_states old_states states =
	let solver = Z3wrapper.config_solver () in
	match states with
	| [] -> []
	| s2::tl2 ->
		let rec entailment_one old_states =
			match old_states with
			| [] -> [s2] (* add new state *)
			| s1::tl1 ->
				if (Abduction.entailment solver s1.State.miss s2.State.miss s2.lvars)
				then
					if (Abduction.entailment solver s1.miss s2.act s2.lvars)
					then (
						prerr_endline ">>> entailment_check: discard state";
						[]) (* not add new state, covered by old state *)
					else entailment_one tl1
				else entailment_one tl1
		in
		(entailment_states old_states tl2) @ (entailment_one old_states)

let entailment_check tbl uid states =
	let found = Hashtbl.find_opt tbl uid in
	match found with
	| None -> Hashtbl.add tbl uid states; states (* first entry *)
	| Some old_states -> prerr_endline ">>> entailment_check: next";
		let new_states = entailment_states old_states states in
		Hashtbl.replace tbl uid (old_states @ new_states); new_states

let find_opt tbl x = Hashtbl.find_opt tbl x

let reset = Hashtbl.reset

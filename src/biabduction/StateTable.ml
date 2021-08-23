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
	mutable rerun: State.t list; (** states that need to be rerun *)
	tbl: st_tbl
}

exception EntailmentLimit

let create fuid = let (bb_tbl : st_tbl) = Hashtbl.create 1 in {fuid=fuid; fst_run=true; rerun=[]; tbl=bb_tbl}

(* entailment check miss1 <= miss2 and curr1 <= curr2 *)
let rec entailment_states old_states states =
	let solver = Z3wrapper.config_solver () in
	match states with
	| [] -> []
	| s2::tl2 ->
		let rec entailment_one old_states =
			match old_states with
			| [] -> [s2] (* add new state *)
			| s1::tl1 ->
				let evars = CL.Util.list_join_unique s2.State.lvars s1.State.lvars in
				if (Abduction.entailment solver s2.miss s1.miss evars)
				then
					if (Abduction.entailment solver s2.curr s1.curr evars)
					then (
						prerr_endline ">>> entailment_check: discard state";
						[]) (* not add new state, covered by old state *)
					else entailment_one tl1
				else entailment_one tl1
		in
		(entailment_one old_states) @ (entailment_states old_states tl2)

(* return added states *)
let add st uid states =
	let found = Hashtbl.find_opt st.tbl uid in
	match found with
	| None -> (* first entry *)
		Hashtbl.add st.tbl uid {cnt=1; states=states}; states
	| Some {cnt=old_cnt; states=old_states} ->
		if (Config.entailment_limit () = old_cnt) then (
			prerr_endline ">>> entailment_check: limit";
			raise_notrace EntailmentLimit
		) else (
			prerr_endline ">>> entailment_check: next";
			let new_states = entailment_states old_states states in
			let value = {cnt=(old_cnt + 1); states=(old_states @ new_states)} in
			Hashtbl.replace st.tbl uid value;
			new_states )

let add_rerun st state = st.rerun <- state::st.rerun

let reset st = Hashtbl.reset st.tbl; st.fst_run <- true; st.rerun <- []

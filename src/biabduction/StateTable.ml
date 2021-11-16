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

exception EntailmentLimit of Config.src_pos

let create fuid = let (bb_tbl : st_tbl) = Hashtbl.create 1 in {fuid=fuid; fst_run=true; rerun=[]; tbl=bb_tbl}

(* Try abstraction on each miss anad act of each state,
   for now only list abstraction *)
let try_abstraction_on_states solver fuid states =
	let pvars = CL.Util.get_pvars fuid in
	let rec try_abstraction states =
		match states with
		| [] -> []
		| s::tl ->
			let new_miss = Abstraction.lseg_abstraction solver s.State.miss pvars in
			let new_curr = Abstraction.lseg_abstraction solver s.curr pvars in
			let abstract_state = {State.miss = new_miss; curr = new_curr; lvars=s.lvars; through_loop = s.through_loop} in
			(* TODO: update lvars *)
			abstract_state :: (try_abstraction tl)
	in
	prerr_endline ">>> trying list abstraction";
	try_abstraction states

(* entailment check miss1 <= miss2 and curr1 <= curr2 *)
let rec entailment_states fuid old_states states =
	let solver = Z3wrapper.config_solver () in
	match states with
	| [] -> []
	| s2::tl2 ->
		let rec entailment_one old_states =
			match old_states with
			| [] -> if Config.abstraction_mode () = 1
				then try_abstraction_on_states solver fuid [s2] (* try abstraction before add new state *)
				else [s2] (* add new state *)
			| s1::tl1 ->
				let evars = CL.Util.list_join_unique s2.State.lvars s1.State.lvars in
				if (Abduction.entailment solver s2.miss s1.miss evars)
				then
					if (Abduction.entailment solver s2.curr s1.curr evars)
					then (
						incr Config.statistics.entailments;
						prerr_endline ">>> entailment_check: discard state";
						[]) (* not add new state, covered by old state *)
					else entailment_one tl1
				else entailment_one tl1
		in
		(entailment_one old_states) @ (entailment_states fuid old_states tl2)

(* return added states *)
let add ?(entailment=false) st uid states =
	let found = Hashtbl.find_opt st.tbl uid in
	match found with
	| None -> (* first entry *)
		Hashtbl.add st.tbl uid {cnt=1; states=states}; states
	| Some {cnt=old_cnt; states=old_states} ->
		if entailment
		then (
			if (Config.entailment_limit () = old_cnt)
			then (
				prerr_endline ">>> entailment_check: limit";
				raise_notrace (EntailmentLimit __POS__)
			) else (
				let astates = (if Config.abstraction_mode () = 2
					then ( (* try abstraction before entailment is called *)
						let solver = Z3wrapper.config_solver () in
						try_abstraction_on_states solver st.fuid states )
					else states (* nothing *) ) in
				prerr_endline (">>> entailment_check: next "^(string_of_int old_cnt));
				let new_states = entailment_states st.fuid old_states astates in
				let value={cnt=(old_cnt+1); states=(old_states @ new_states)} in
				Hashtbl.replace st.tbl uid value;
				List.map State.set_through_loop new_states )
		) else states (* nothing TODO bound *)

let add_rerun st c = st.rerun <- c::st.rerun

let reset st = Hashtbl.reset st.tbl; st.fst_run <- true; st.rerun <- []

let start_rerun st =
	let rerun_contracts = st.rerun in
	reset st; st.fst_run <- false;
	rerun_contracts

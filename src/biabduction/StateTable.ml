(*
 *  Copyright (C) Broom team
 *
 *  This file is part of Broom.
 *
 *  Broom is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  Broom is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <https://www.gnu.org/licenses/>.
 *)

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
	mutable rerun: State.t list;
	(** if [fst_run], contracts that need to be rerun
	    else possible final contracts of one of rerun at the time *)
	tbl: st_tbl
}

exception EntailmentLimit of CL.Loc.t option

let create fuid = let (bb_tbl : st_tbl) = Hashtbl.create 1 in {fuid=fuid; fst_run=true; rerun=[]; tbl=bb_tbl}

(* Try abstraction on each miss anad act of each state,
   for now only list abstraction *)
let try_abstraction_on_states solver fuid states =
	let pvars = CL.Util.get_pvars fuid in
	let rec try_abstraction states =
		match states with
		| [] -> []
		| s::tl ->
			let new_miss,new_lvars1 = Abstraction.lseg_abstraction solver s.State.miss pvars in
			let new_curr,new_lvars2 = Abstraction.lseg_abstraction solver s.curr pvars in
			let new_lvars=CL.Util.list_join_unique s.lvars
				(CL.Util.list_join_unique new_lvars1 new_lvars2) in
			let abstract_state = {State.miss = new_miss; curr = new_curr; lvars=new_lvars; through_loop = s.through_loop} in
			abstract_state :: (try_abstraction tl)
	in
	Config.debug2 ">>> trying list abstraction";
	try_abstraction states

let rec entailment_one_side side_fnc s solver states = 
	match states with 
	| [] -> [s]
	| s1 :: tl1 -> 
		let evars = CL.Util.list_join_unique s.State.lvars s1.State.lvars in
				if (Abduction.entailment solver (side_fnc s) (side_fnc s1) evars)
				then []
				else entailment_one_side side_fnc s solver tl1

let rec entailment_incr fuid s2 solver states =
	match states with
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
					Config.debug2 ">>> entailment_check: discard state";
					[]) (* not add new state, covered by old state *)
				else entailment_incr fuid s2 solver tl1
			else entailment_incr fuid s2 solver tl1

(* entailment check based on 'entailment_fnc' *)
let rec entailment_states states states_to_filter entailment_fnc =
	let solver = Z3wrapper.config_solver () in
	match states_to_filter with
	| [] -> []
	| s2::tl2 ->
		(entailment_fnc s2 solver states) @ (entailment_states states tl2 entailment_fnc)		

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
				Config.debug2 ">>> entailment_check: limit";
				raise_notrace (EntailmentLimit (CL.Util.get_block_loc uid))
			) else (
				let astates = (if Config.abstraction_mode () = 2
					then ( (* try abstraction before entailment is called *)
						let solver = Z3wrapper.config_solver () in
						try_abstraction_on_states solver st.fuid states )
					else states (* nothing *) ) in
				Config.debug2 (">>> entailment_check: next "^(string_of_int old_cnt));
				let new_states = entailment_states old_states astates (entailment_incr st.fuid) in
				let value={cnt=(old_cnt+1); states=(old_states @ new_states)} in
				Hashtbl.replace st.tbl uid value;
				List.map State.set_through_loop new_states )
		) else states (* nothing TODO bound *)

let add_rerun st s = 
	let side_fnc =  
		if st.fst_run then fun x -> x.State.miss else fun x -> x.State.curr in
	(* pruning of contracts *)
	let stay = entailment_states [s] st.rerun (entailment_one_side side_fnc) in
	st.rerun <- s::stay
	

let reset ?(fst=true) st =
	Hashtbl.reset st.tbl;
	st.fst_run <- fst;
	st.rerun <- []

let reset_rerun st = reset ~fst:false st

let start_rerun st =
	let rerun_contracts = st.rerun in
	reset_rerun st;
	rerun_contracts

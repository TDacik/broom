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
	mutable rerun: Contract.t list;
	(** if [fst_run], contracts that need to be rerun
	    else possible final contracts of one of rerun at the time *)
	tbl: st_tbl
}

exception EntailmentLimit of CL.Loc.t option

val create : cl_uid -> t

(** [add entailment tbl uid states] if entailment is true, returns subset of
    [states] not covered by previous runs, where [uid] is basic block at the
    beginning of which we add [states]
    otherwise joint [states] with all from previous runs
 *)
val add : ?entailment:bool -> t -> cl_uid -> State.t list -> State.t list

(** [add_rerun tbl contract] adds [contract] which needs to be rerun or
    [contracts] which are possible final after rerun *)
val add_rerun : t -> Contract.t -> unit

val start_rerun : t -> Contract.t list

val reset : ?fst:bool -> t -> unit

val reset_rerun : t -> unit

(** [try_abstraction_on_states solver fuid states] tries abstraction on each
    miss anad act of each state, for now only list abstraction *)
val try_abstraction_on_states : Z3wrapper.solver -> cl_uid -> State.t list ->
                                State.t list

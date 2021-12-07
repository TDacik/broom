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

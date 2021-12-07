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

(** type for location in source code: __POS__ *)
type src_pos = string * int * int * int

(** [src_pos_to_string pos] gets location in source code as a string
    file - filename
    lnum - number of line number
    cnum - the character position in the line
    enum - the last character position in the line. *)
val src_pos_to_string: (string * int * int * int) -> string

(** [loc_to_string loc] gets CL code location as string *)
val loc_to_string: Loc.t option -> string

val internal: string * src_pos -> unit

val error: string * Loc.t option -> unit

val warn: string * Loc.t option -> unit

val note: string * Loc.t option -> unit

(** [internal_fail (msg,loc)] *)
val internal_fail: string * src_pos -> 'a

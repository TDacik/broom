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

(** Get location in source code as a string
    file - filename
    lnum - number of line number
    cnum - the character position in the line
    enum - the last character position in the line. *)
let src_pos_to_string (file,lnum,cnum,_) =
	file^":"^(string_of_int lnum)^":"^(string_of_int cnum)^":"

let loc_to_string loc =
	match loc with
	| Some (file, line, column, _) ->
		file^":"^(string_of_int line)^":"^(string_of_int column)^":"
	| None -> ""

let internal (str,loc) =
	let msg = (src_pos_to_string loc)^"internal error: "^str in
	if (Unix.isatty Unix.stderr)
		then prerr_endline ("\027[1;31m"^msg^"\027[0m")
		else prerr_endline msg

let error (str,loc) =
	let msg = (loc_to_string loc)^"error: "^str in
	if (Unix.isatty Unix.stderr)
		then prerr_endline ("\027[1;31m"^msg^"\027[0m")
		else prerr_endline msg

let warn (str,loc) =
	let msg = (loc_to_string loc)^"warning: "^str in
	if (Unix.isatty Unix.stderr)
		then prerr_endline ("\027[1;35m"^msg^"\027[0m")
		else prerr_endline msg

(* TODO change color *)
let note (str,loc) =
	let msg = (loc_to_string loc)^"note: "^str in
	if (Unix.isatty Unix.stderr)
		then prerr_endline ("\027[1;35m"^msg^"\027[0m")
		else prerr_endline msg

(* TODO: only if develop mode *)
let internal_fail (msg,loc) = failwith ((src_pos_to_string loc)^" "^ msg)

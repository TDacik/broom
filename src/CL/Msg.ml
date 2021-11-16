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

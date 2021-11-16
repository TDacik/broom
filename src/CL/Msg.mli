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

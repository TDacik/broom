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

(** {1 Statistics *)

type stat = {
  abstracts : int ref;    (** Number of successful abstractions *)
  entailments : int ref;  (** Number of successful entailments *)
  badrerun : int ref;     (** Number of discard preconditions after rerun *)
  internals : int ref;    (** Number of internal errors *)
  errs : int ref;         (** Number of errors in code *)
  warns : int ref;        (** Number of warnings *)
}

val statistics : stat

(** If option [--display-stats] prints statistics on failures and statistics
    about execution process, see {!stat} *)
val display_stats : unit -> unit


(** {1 Errors handling} *)

(** Type for location in source code: __POS__ *)
type src_pos = CL.Msg.src_pos

(** Print internal error message using the given internal location on stderr *)
val prerr_internal : string -> src_pos -> unit

(** Print error message using the given location info on stderr *)
val prerr_error : string -> CL.Loc.t option -> unit

(** Print warning message using the given location info on stderr *)
val prerr_warn : string -> CL.Loc.t option -> unit

(** Print note message using the given location info on stderr *)
val prerr_note : string -> CL.Loc.t option -> unit

(** {1 Options} *)

(** Describe verbose level as follow:
  - 0 no debug information
  - 1 print name of analysed function (default)
  - 2 + print information about expensive operations: abstraction/entailment
  - 3 + print current state for every instruction
  - 4 + print contract and abduction info for every instruction

  Information are printing on stderr.
  Could by change by option [--verbose <uint>].
*)
val verbose : unit -> int

(** Print on stderr, if {!verbose} level is 1 or higher. *)
val debug1 : string -> unit

(** Print on stderr, if {!verbose} level is 2 or higher. *)
val debug2 : string -> unit

(** Print on stderr, if {!verbose} level is 3 or higher. *)
val debug3 : string -> unit

(** Print on stderr (no new line), if {!verbose} level is 4. *)
val debug4_string : string -> unit

(** Print on stderr, if {!verbose} level is 4. *)
val debug4 : string -> unit


(** Set by option [--main=<name>]. It is a name of entry function -
    initializing global variables and expecting 0 or 2 arguments (argv, argc),
    Default: main *)
val main : unit -> string

(* Set by option [--only-fnc=<name>]. It is a name of the function that will be
   the only one to be analyzed, except for the functions called by this
   function. *)
(* val only_fnc : unit -> string *)

(** If true, preconditions of function will be rerun when nondeterminismus or
    abstraction happend or go through the loops. Default: true

    Could be disabled by option [--no-rerun] *)
val rerun : unit -> bool

(** EXPERIMENTAL: Set by option [--oom] (out of memory). Simulate possible
    shortage of memory
    (heap allocation e.g. [malloc], [calloc] can fail). Default: false *)
val oom : unit -> bool

(** Set by [--exit-leaks] or [--no-exit-leaks]. If true, reports memory leaks
    of static variables at the end of program (while executing a no-return
    function or {!main}), Default: true *)
val exit_leaks : unit -> bool

(** Set by [--memory-leaks-as-errors]. If true, reports memory leaks as errors
    otherwise warnings. Default: false *)
val memory_leaks_as_errors : unit -> bool

(** EXPERIMENTAL: Set by [--close-lambda]. If true, close lambdas are used
    within the abstraction. Default: false *)
val close_lambda :  unit -> bool

(** Set by [--abstraction-mode <uint>]. Using of Slseg (Singly-linked List
    Segment) and Dlseg (Double-linked List Segment) abstraction:
    - 0 - disabeled
    - 1 - after entailment unssucced (default)
    - 2 - before entailment *)
val abstraction_mode : unit -> int

(** Set by [--abstract-on-call]. Additionally perform abstraction after each
    just completed call on caller's side. Default: false *)
val abstract_on_call_done : unit -> bool

(** If true, entailment states when traversing a loop-closing edge,
    else on each basic block entry. Default: true *)
val entailment_on_loop_edges_only : unit -> bool

(** Set by [--entailment-limit <uint>]. Number of loop unfoldings used to stop
    the loop analysis when a fixpoint is not computed within a given number of
    loop iterations. 0 means no limit. Default: 5 *)
val entailment_limit : unit -> int

(** Set by [--abduction-strategy <uint>]. Abduction strategies are:
    - 0 - single strategy = one result (default)
    - 1 - more strategies = possible more restults
*)
val abduction_strategy : unit -> int

(** Set by [--timeout <uint>]. Solver timeout for symbolic execution (in
    miliseconds). 0 means no timeout. Default: 2000ms *)
val solver_timeout : unit -> int

(** Set by [--timeout-simplify <uint>]. Solver timeout for formula
    simplification in states (in miliseconds). 0 means no timeout.
    Default: 100ms *)
val solver_timeout_simplify : unit -> int

(** Set by [--timeout-abstraction <uint>]. Solver timeout for widening (in
    miliseconds). 0 means no timeout. Default: 200ms *)
val solver_timeout_abstraction : unit -> int

(** Set by [--print-cl]. Dump linearised {!CL} code on standard output.
    Defalt: false *)
val print_cl : unit -> bool

(** Set by [--print-contracts]. Dump linearised {!CL} code with contracts on
    standard output. Defalt: false *)
val print_contracts : unit -> bool

(** Set by [--dry-run]. Do not run the analysis. Defalt: false *)
val dry_run : unit -> bool

(** {1 Parsing command line *)

(** Parse the command line arguments. *)
val analyse_cmd_arguments : unit -> unit

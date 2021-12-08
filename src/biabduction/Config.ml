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

(* module Debug = struct (* --debug *)
  type t =
      Next
    | Skip
    | Finish

let debug_of_string = function
  | "n" | "next" -> Next
  | "s" | "skip" -> Skip
  | "f" | "finish" -> Finish
  | _ -> assert false

let contracts = true

let abduction = false

let abstraction = true

let steps = Finish (* --steps=n|s|f *)

(* let printf fmt =
  if debug () then Printf.printf fmt (* else ignore *) *)

end *)

(** Statistics *)

type stat = {
  abstracts : int ref;
  entailments : int ref;
  badrerun : int ref;
  internals : int ref;
  errs : int ref;
  warns : int ref;
}

let statistics = {abstracts = ref 0; entailments = ref 0; badrerun = ref 0; internals = ref 0; errs = ref 0; warns = ref 0 }

(** --stats *)
let _stats = ref false
let stats () = !_stats

let display_stats () =
  if stats () then (
    (* Printf.printf "Number of abstractions: %i\n" !(statistics.abstracts); *)
    Printf.printf "Number of successful entailments: %i\n" !(statistics.entailments);
    Printf.printf "Number of discard preconditions after rerun : %i\n" !(statistics.badrerun);
    Printf.printf "Number of internals: %i\n" !(statistics.internals);
    Printf.printf "Number of errors: %i\n" !(statistics.errs);
    Printf.printf "Number of warnings: %i\n" !(statistics.warns);
  )


(** Errors handling *)

(** type for location in source code: __POS__ *)
type src_pos = CL.Msg.src_pos

let prerr_internal str loc =
  incr statistics.internals;
  CL.Msg.internal (str,loc)

let prerr_error str loc =
  incr statistics.errs;
  CL.Msg.error (str,loc)

let prerr_warn str loc =
  incr statistics.warns;
  CL.Msg.warn (str,loc)

let prerr_note str loc =
  CL.Msg.note (str,loc)

(** Options *)

(** describe verbose level as follow:
  - 0 no debug information
  - 1 print name of analysed function
  - 2 + print information about expensive operations: abstraction/entailment
  - 3 + print current state for every instruction
  - 4 + print contract and abduction info for every instruction
      information are printing on stderr
*)
let _verbose = ref 1
let verbose () = !_verbose

let debug1 str =
  if 1 <= verbose () then prerr_endline str

let debug2 str =
  if 2 <= verbose () then prerr_endline str

let debug3 str =
  if 3 <= verbose () then prerr_endline str

let debug4_string str =
  if 4 <= verbose () then (prerr_string str; flush stderr;)

let debug4 str =
  if 4 <= verbose () then prerr_endline str


(** --main=<name> set name of entry function - initializing global variables and
    expecting 0 or 2 arguments (argv, argc) *)
let _main = ref "main"
let main () = !_main

(* --only-fnc=<name> set the name of the function that will be the only one to
   be analyzed, except for the functions called by this function *)
(* let only_fnc () = "main" *)

(** if true preconditions of function will be rerun when nondeterminismus or
   abstraction happend or go through the loops *)
let _rerun = ref true
let rerun () = !_rerun

(** --oom / --out-of-memory unsuccesful heap allocation *)
(* TODO fix rerun *)
let _oom = ref false
let oom () = !_oom

(** --exit-leaks report memory leaks of static variables at the end of program
   (while executing a no-return function or main) *)
let _exit_leaks = ref true
let exit_leaks () = !_exit_leaks

(** --memory_leaks_as_errors report memory leaks as errors otherwise warnings *)
let _memory_leaks_as_errors = ref false
let memory_leaks_as_errors () = !_memory_leaks_as_errors

(* do not use Slseg (Singly-linked List Segment) abstraction *)
(* let disable_sls = false *)

(* do not use Dlseg (Double-linked List Segment) abstraction *)
(* let disable_dls = false *)

(** EXPERIMENTAL: close lambdas within the abstraction *)
let _close_lambda = ref false
let close_lambda () = !_close_lambda

(** using of Slseg (Singly-linked List Segment) and Dlseg (Double-linked List
   Segment) abstraction:
   - 0 - disabeled
   - 1 - after entailment unssucced
   - 2 - before entailment *)
let _abstraction_mode = ref 1
let abstraction_mode () = !_abstraction_mode

(** additionally perform abstraction after each just completed call on caller's
   side *)
let _abstract_on_call_done = ref false
let abstract_on_call_done () = !_abstract_on_call_done

(** if true entailment states when traversing a loop-closing edge,
   else on each basic block entry *)
let entailment_on_loop_edges_only () = true

(** max number of entailment calls for one loop : 0 - no limit *)
let _entailment_limit = ref 5
let entailment_limit () = !_entailment_limit

(** Abduction strategy:
    - 0 - single strategy = one result,
    - 1 - more strategies = possible more restults
*)
let _abduction_strategy = ref 0
let abduction_strategy () = !_abduction_strategy

(** Solver timeout (in miliseconds) : 0 - no timeout *)
let _solver_timeout = ref 2000
let solver_timeout () = !_solver_timeout

(** Solver timeout for symplify states (in miliseconds) : 0 - no timeout *)
let _solver_timeout_simplify = ref 100
let solver_timeout_simplify () = !_solver_timeout_simplify

(** Solver timeout for abstraction (in miliseconds) : 0 - no timeout *)
let _solver_timeout_abstraction = ref 200
let solver_timeout_abstraction () = !_solver_timeout_abstraction

let _print_cl = ref false
let print_cl () = !_print_cl

let _print_contracts = ref false
let print_contracts () = !_print_contracts

let _dry_run = ref false
let dry_run () = !_dry_run

(* no additional options or files *)
let _rest_arg f = if (f != "") then raise (Arg.Bad "too many arguments")

let usage_msg = "\
Usage: broom [options] -- file
"

let show_version_and_die () =
  print_endline Version.curr;
  exit 0

let analyse_cmd_arguments () = Arg.(
    let options = [
      "--verbose", Set_int _verbose,
      " Turn on verbose mode (0-4)";

      "--main", Set_string _main,
      " set name of entry function for initialization of global variables (default is main)";

      "--no-rerun", Clear _rerun,
      " Diseable second run";

      "--oom", Set _oom,
      " Out of memory (heap allocation can fail)";

      "--exit-leaks", Set _exit_leaks,
      " Report memory leaks while executing a no-return function";

      "--no-exit-leaks", Clear _exit_leaks,
      " Not report memory leaks while executing a no-return function";

      "--memory_leaks_as_errors", Set _memory_leaks_as_errors,
      " Report memory leaks as errors otherwise warnings";

      "--abstraction-mode ", Set_int _abstraction_mode,
      " Abstraction of list segment is 0 - desabled, 1 - after entailment unssucced (default), 2 - before entailment";

      "--close-lambda", Set _close_lambda,
      " EXPERIMENTAL: proceed close lambdas within the abstraction";

      "--abstract-on-call", Set _abstract_on_call_done,
      " Perform abstraction after each just completed call";

      "--entailment-limit", Set_int _entailment_limit,
      " Max number of entailment calls for one loop (default is 5)";

      "--abduction-strategy", Set_int _abduction_strategy,
      " Abduction strategy: 0 for one result (default), 1 for multiple results";

      "--timeout", Set_int _solver_timeout,
      " Set Z3 timeout (in ms)";

      "--timeout-simplify", Set_int _solver_timeout_simplify,
      " Set Z3 timeout for simplify states (in ms)";

      "--timeout-abstraction", Set_int _solver_timeout_abstraction,
      " Set Z3 timeout for abstraction (in ms)";

      "--display-stats", Set _stats,
      " Display statistics";

      "--print-cl", Set _print_cl,
      " Dump linearised CL code on standard output";

      "--print-contracts", Set _print_contracts,
      " Dump linearised CL code with contracts on standard output";

      "--dry-run", Set _dry_run,
      " Do not run the analysis";

      "--version", Unit show_version_and_die,
      " Show version number and exit"
    ]
    in
    parse (align options) _rest_arg usage_msg
  )
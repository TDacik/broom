module Debug = struct (* --debug *)
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

end


type stat = {
  abstracts : int ref;
  entailments : int ref;
  sat_fail : int ref;
  internals : int ref;
  errs : int ref;
  warns : int ref;
}

let statistics = {abstracts = ref 0; entailments = ref 0; sat_fail = ref 0; internals = ref 0; errs = ref 0; warns = ref 0 }

(* --stats *)
let stats () = false

let display_stats () =
  if stats () then (
    Printf.printf "Number of abstractions: %i\n" !(statistics.abstracts);
    Printf.printf "Number of successful entailments: %i\n" !(statistics.entailments);
    Printf.printf "Number of unsatisfiable states: %i\n" !(statistics.sat_fail);
    Printf.printf "Number of internals: %i\n" !(statistics.internals);
    Printf.printf "Number of errors: %i\n" !(statistics.errs);
    Printf.printf "Number of warnings: %i\n" !(statistics.warns);
  )


(* errors handling *)
(* TODO: location *)
let prerr_internal str =
  incr statistics.internals;
  if (Unix.isatty Unix.stderr)
    then prerr_endline ("\027[1;31m!!! internal error: "^str^"\027[0m")
    else prerr_endline ("!!! internal error: "^str)

let prerr_error str =
  incr statistics.errs;
  if (Unix.isatty Unix.stderr)
    then prerr_endline ("\027[1;31m!!! error: "^str^"\027[0m")
    else prerr_endline ("!!! error: "^str)

let prerr_warn str =
  incr statistics.warns;
  if (Unix.isatty Unix.stderr)
    then prerr_endline ("\027[1;35m!!! warning: "^str^"\027[0m")
    else prerr_endline ("!!! warning: "^str)

let prerr_note str =
  if (Unix.isatty Unix.stderr)
    then prerr_endline ("\027[1;35m!!! note: "^str^"\027[0m")
    else prerr_endline ("!!! note: "^str)

(* 0x0 no debug
   0x1 debug contracts
   0x2 debug abduction
   0x4 debug abstraction
   0x8 stats? *)
let verbose = 0xD

(* --main=<name> set name of entry function - initializing global variables and
   expecting 0 or 2 arguments (argv, argc) *)
let main () = "main"

(* if true summery of function will be rerun when abstraction happend or go
   through the loops *)
let rerun () = true

(* --oom / --out-of-memory unsuccesful heap allocation *)
let oom = false

(* --exit-leaks report memory leaks of static variables at the end of program
   (while executing a no-return function or main) *)
let exit_leaks () = true

(* --memory_leaks_as_errors report memory leaks as errors otherwise warnings *)
let memory_leaks_as_errors () = false

(* do not use Slseg (Singly-linked List Segment) abstraction *)
let disable_sls = false

(* do not use Dlseg (Double-linked List Segment) abstraction *)
let disable_dls = false

(* do not perform abstraction on each end of basic blocks, but only when
   looping *)
let abstract_on_loop_edges_only = true

(* perform abstraction after each just completed call on caller's side *)
let abstract_on_call_done = false

(* if true entailment states when traversing a loop-closing edge,
   else on each basic block entry *)
let entailment_on_loop_edges_only = false

(* max number of entailment calls for one loop : 0 - no limit *)
let entailment_limit () = 5

(* Abduction strategy: 0 - single strategy = one result,
                       1 - more strategies = possible more restults
*)
let abduction_strategy = 0

(* Solver timeout (in miliseconds) : 0 - no timeout *)
let solver_timeout = 2000
let solver_timeout_simplify = 100
let solver_timeout_abstraction = 200
                   

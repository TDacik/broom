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

(* errors handling *)
(* TODO: location *)
let prerr_internal str =
  if (Unix.isatty Unix.stderr)
    then prerr_endline ("\027[1;31m!!! internal error: "^str^"\027[0m")
    else prerr_endline ("!!! internal error: "^str)

let prerr_error str =
  if (Unix.isatty Unix.stderr)
    then prerr_endline ("\027[1;31m!!! error: "^str^"\027[0m")
    else prerr_endline ("!!! error: "^str)

let prerr_warn str =
  if (Unix.isatty Unix.stderr)
    then prerr_endline ("\027[1;35m!!! warning: "^str^"\027[0m")
    else prerr_endline ("!!! warning: "^str)

let prerr_note str =
  if (Unix.isatty Unix.stderr)
    then prerr_endline ("\027[1;35m!!! note: "^str^"\027[0m")
    else prerr_endline ("!!! note: "^str)


type stat = {
	abstracts : int;
	entailments : int;
	sat_fail : int;
	errs : int;
	warns : int;
}

let stats = true (* --stats *)

(* let errs = ref 0
incr errs; *)

let display_stats stat = 
  if stats then (
    Printf.printf "Number of abstractions: %i\n" !stat.abstracts;
    Printf.printf "Number of successful entailments: %i\n" !stat.entailments;
    Printf.printf "Number of unsatisfiable states: %i\n" !stat.sat_fail;
    Printf.printf "Number of errors: %i\n" !stat.errs;
	Printf.printf "Number of warnings: %i\n" !stat.warns;
  )

(* 0x0 no debug
   0x1 debug contracts
   0x2 debug abduction
   0x4 debug abstraction
   0x8 stats? *)
let verbose = 0xD

(* --main=<name> set name of entry function - initializing global variables and
   expecting 0 or 2 arguments (argv, argc) *)
let main = "main"

(* --oom / --out-of-memory unsuccesful heap allocation *)
let oom = false

(* --exit-leaks report memory leaks of static variables at the end of program
   (while executing a no-return function or main) *)
let exit_leaks () = true

let memory_leaks_as_errors = false

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

(* max number of entailment calls for one loop *)
let entailment_limit () = 5


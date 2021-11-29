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
  badrerun : int ref;
  internals : int ref;
  errs : int ref;
  warns : int ref;
}

let statistics = {abstracts = ref 0; entailments = ref 0; badrerun = ref 0; internals = ref 0; errs = ref 0; warns = ref 0 }

(* --stats *)
let stats () = true

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

(* describe verbose level as follow:
  0 no debug information
  1 print name of analysed function
  2 + print information about expensive operations: abstraction/entailment
  3 + print contract, abduction info, and current state for every instruction
  information are printing on stderr
*)
let verbose () = 2

let debug1 str =
  if 1 <= verbose () then prerr_endline str

let debug2 str =
  if 2 <= verbose () then prerr_endline str

let debug3 str =
  if 3 <= verbose () then prerr_endline str

let debug3_string str =
  if 3 <= verbose () then (prerr_string str; flush stderr;)


(* --main=<name> set name of entry function - initializing global variables and
   expecting 0 or 2 arguments (argv, argc) *)
let main () = "main"

(* --only-fnc=<name> set the name of the function that will be the only one to
  be analyzed, except for the functions called by this function *)
(* let only_fnc () = "main" *)

(* if true preconditions of function will be rerun when nondeterminismus or
   abstraction happend or go through the loops *)
let rerun () = true

(* --oom / --out-of-memory unsuccesful heap allocation *)
let oom = false

(* --exit-leaks report memory leaks of static variables at the end of program
   (while executing a no-return function or main) *)
let exit_leaks () = true

(* --memory_leaks_as_errors report memory leaks as errors otherwise warnings *)
let memory_leaks_as_errors () = false

(* do not use Slseg (Singly-linked List Segment) abstraction *)
(* let disable_sls = false *)

(* do not use Dlseg (Double-linked List Segment) abstraction *)
(* let disable_dls = false *)

(* EXPERIMENTAL: close lambdas within the abstraction *)
let close_lambda () = false

(* using of Slseg (Singly-linked List Segment) and Dlseg (Double-linked List
  Segment) abstraction:
  0 - disabeled
  1 - after entailment unssucced
  2 - before entailment *)
let abstraction_mode () = 1

(* additionally perform abstraction after each just completed call on caller's
   side *)
let abstract_on_call_done () = false

(* if true entailment states when traversing a loop-closing edge,
   else on each basic block entry *)
let entailment_on_loop_edges_only () = true

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
                   

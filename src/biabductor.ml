(* Sample main file for the executable.

   Doesn't contain any useful content yet. I just wanted to understand
   how to specify libraries and executables in dune.

*)

open Format

open Z3
(* The following would have to be here if we removed (wrapped false)
   from lib/dune. If I do that, however, the runtest target breaks
   because the default test extraction does not preface to module
   names with Llbiabd._, so OCaml complains that it does not know the
   modules. For now I'll keep it this way. *)
(*open Llbiabd*)
open Z3wrapper
open Formula

let cfg = [("model", "true"); ("proof", "false")]
let ctx = (mk_context cfg)
let solv = (Solver.mk_solver ctx None)

let () =
  let x = Z3wrapper.formula_to_solver ctx Formula.form1 in
  printf "Test 1\n";
  Z3.Solver.add solv x;
  printf "Test 2\n";
  let res = Z3.Solver.check solv [] in
  printf "Hello, %s!\n" (Z3.Solver.string_of_status res);
  let b = Exp.Bool false in
  printf "The const is %s\n" (Exp.to_string (Const b));
  let z3b = const_to_solver ctx b in
  let _ = Z3.Solver.check solv [z3b] in
  printf "That's it\n"

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
open Biabd
open Z3wrapper
open Formula
open Abstraction

let cfg = [("model", "true"); ("proof", "false")]
let ctx = (mk_context cfg)
let solv = (Solver.mk_solver ctx None)
let z3_names=get_sl_functions_z3 ctx

let ptr_size=Exp.Const (Int 8L)

let form1 = {
    sigma = [ Hpointsto (Var 1, ptr_size, Var 2) ];
    pi = [ BinOp ( Peq, Var 1, UnOp ( Base, Var 1));
          BinOp ( Peq, UnOp ( Len, Var 1), Const (Int 8L));
          BinOp ( Peq, Var 1, Var 2332 );
          BinOp ( Peq, Var 2, Exp.null) ]
    (*evars = [ 2 ]*)
}

let () =
let ptr_size=Exp.Const (Exp.Int (Int64.of_int 8)) in
 let form5=
  let lambda= {param=[1;2] ;form={
      sigma = [ Hpointsto (Var 1, ptr_size, Var 2); Hpointsto (Var 2, ptr_size, Var 3) ]; pi=[] }}
  in
  {
          sigma = [ Hpointsto (Var 1, ptr_size, Var 2); Hpointsto (Var 6, ptr_size, Var 5); Slseg (Var 3, Var 4, lambda) ];
      pi = [ BinOp ( Peq, Var 1, UnOp ( Base, Var 1));
            BinOp ( Peq, UnOp ( Len, Var 1), Const (Int (Int64.of_int 16)));
           BinOp ( Peq, Var 6, (BinOp (Pplus, Var 1, (Const (Int (Int64.of_int 7))))));
            BinOp ( Peq, Var 1, Var 2332 );
            BinOp ( Peq, Var 2, Exp.null) ]
  }
in 

print_with_lambda form5;
let z3_form5=formula_to_solver ctx form5 in
if (Solver.check solv z3_form5)=SATISFIABLE then print_string "OK\n" else print_string "NO\n";
print_with_lambda form_abstr12;
let aa=try_abstraction_to_lseg ctx solv z3_names form_abstr12 0 1 [1]
in match aa with
| AbstractionFail -> print_string "FF\n"
| AbstractionApply x -> print_string "AA";print_with_lambda x






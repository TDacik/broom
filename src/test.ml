(* Sample main file for the executable.

   Doesn't contain any useful content yet. I just wanted to understand
   how to specify libraries and executables in dune.

*)

(* open Format *)

(* open Z3 *)
(* The following would have to be here if we removed (wrapped false)
   from lib/dune. If I do that, however, the runtest target breaks
   because the default test extraction does not preface to module
   names with Llbiabd._, so OCaml complains that it does not know the
   modules. For now I'll keep it this way. *)
(*open Llbiabd*)
open Biabd
(* open Z3wrapper *)
open Formula
(* open Abstraction *)

(* let cfg = [("model", "true"); ("proof", "false")]
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
} *)

let gvars = [-1; 5]
let evars = [2; 3; 4; 6; 7]

let form_false = {
    sigma = [];
    pi = [  Const (Bool false); Exp.BinOp ( Plesseq, Exp.one, Exp.zero) ]
}

(* 1=2 2=3 6=5 4=4 4=5 *)
let form_eq = {
    sigma = [ Hpointsto (Var (-1), Const (Int 4L), Const (Int 8L))];
    pi = [
		Exp.BinOp ( Peq, Var (-1), Var 2);
		Exp.BinOp ( Peq, Var 2, Var 3);
		Exp.BinOp ( Peq, Var 5, Var 6);
		Exp.BinOp ( Peq, Var 4, Var 4);
		Exp.BinOp ( Peq, Var 4, Var 5);
		Exp.BinOp ( Peq, Var 7, Var 7)
		]
}

let form_eq2 = {
    sigma = [ Hpointsto (Var 4, Const (Int 8L), Var 4)];
    pi = [Exp.BinOp ( Peq, Var 2, Var 3)]
}


let () =
(* let ptr_size=Exp.Const (Exp.Int (Int64.of_int 8)) in
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
| AbstractionApply x -> print_string "AA";print_with_lambda x *)
(* print_endline ("form_false: " ^ (to_string form_false));
let form_new = remove_useless_conjuncts form_false [] in
print_endline ("form_new: " ^ (to_string form_new)) *)

print_endline ("form_eq: " ^ (to_string form_eq));
(* let form_simp_ll = simplify_ll gvars evars form_eq in *)
(* print_endline ("form_simp_ll: " ^ (to_string form_simp_ll));
let pi_remove_eq = remove_redundant_eq form_simp_ll.pi in
let form_remove_eq = {pi = pi_remove_eq; sigma = form_simp_ll.sigma} in
print_endline ("form_remove_eq: " ^ (to_string form_remove_eq)); *)
let form_ren = remove_equiv_vars gvars evars form_eq in
print_endline ("form_ren: " ^ (to_string form_ren));


let state = {State.miss = form_eq; curr = form_eq2; lvars = evars} in
print_endline ("state: " ^ (State.to_string state));
let state_ren = State.remove_equiv_vars gvars evars state in
(* let state_ren = State.simplify state in *)
print_endline ("state_ren: " ^ (State.to_string state_ren));



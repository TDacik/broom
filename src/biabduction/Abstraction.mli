(* open Formula
open Z3
open Z3wrapper *)

exception ErrorInAbstraction of string

(** [lseg_abstaction ctx solv z3_names form pvars] tries list abstraction on formula [form] - first tries the last added, at least 2 predicates in sigma *)
val lseg_abstaction : Z3.context -> Z3.Solver.solver ->
           Z3wrapper.sl_function_names_z3 ->
           Formula.t -> Formula.Exp.variable list -> Formula.t

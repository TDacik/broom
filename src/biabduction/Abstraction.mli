(* open Formula
open Z3
open Z3wrapper *)

exception ErrorInAbstraction of (string * Config.src_pos)

(** [lseg_abstaction solver form pvars] tries list abstraction on formula [form] - first tries the last added, at least 2 predicates in sigma *)
val lseg_abstraction : Z3wrapper.solver ->
           Formula.t -> Formula.Exp.variable list -> Formula.t

(* Temporaryli added *)
type res =
| AbstractionApply of Formula.t
| AbstractionFail


val try_abstraction_to_lseg: Z3wrapper.solver ->
           Formula.t -> int -> int -> Formula.Exp.variable list -> res

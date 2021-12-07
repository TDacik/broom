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

type variable = Formula.Exp.variable

type split_record =
  | Record of Formula.heap_pred * Formula.t * Formula.pi
  | NoRecord


(** The result is:  "missing, frame, added_lvars, recorded split-rights" *)
type abduction_res =
  | Bok of (Formula.t * Formula.t * variable list * split_record list) list
  | BFail

(** Raise in case of ... *)
(* TODO perhaps ErrorInAbdaction ? *)
exception TempExceptionBeforeApiCleanup of string

(** [biabduction solver fst_run form1 form2] is main biabduction function
    The result is:  "missing, frame, added_lvars"
    First test SAT of form1 and form2.
    Postponing SAT to the end of biabduction may lead to hidden conflicts.
    The conflicts may be removed by application of a match rule.
    Then is a given list of possible rules and the order in which they are
    going to be applied. Trying the rules till an applicable if founded
    if not [fst_run] learn rules are omitted
*)
val biabduction : Z3wrapper.solver -> bool -> Formula.t -> Formula.t ->
                  variable list -> abduction_res


(** [entailment solver form1 form2 evars] checks entailment form1 |= form2 using
    match1 rules
*)
val entailment : Z3wrapper.solver -> Formula.t -> Formula.t -> variable list
    -> bool

val check_lambda_entailment : Z3wrapper.solver -> Formula.lambda ->
	                          Formula.lambda -> int -> int


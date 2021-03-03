type variable = Formula.Exp.variable

type split_record =
  | Record of Formula.heap_pred * Formula.t * Formula.pi
  | NoRecord


(** The result is:  "missing, frame, added_lvars, recorded split-rights" *)
type abduction_res =
  | Bok of Formula.t * Formula.t * variable list * split_record list
  | BFail

(** Raise in case of ... *)
exception TempExceptionBeforeApiCleanup of string

(** Raise in case of ... *)
exception ShouldBeRefactoredToMakeExhaustive of unit

(** Raise in case of ... *)
exception IllegalArgumentException of string

exception NoApplicableRule

(** [biabduction solver form1 form2] is main biabduction function
    The result is:  "missing, frame, added_lvars"
    First test SAT of form1 and form2.
    Postponing SAT to the end of biabduction may lead to hidden conflicts.
    The conflicts may be removed by application of a match rule.
    Then is a given list of possible rules and the order in which they are
    going to be applied. Trying the rules till an applicable if founded
*)
val biabduction : Z3wrapper.solver -> Formula.t -> Formula.t -> variable list
    -> abduction_res


(** [entailment solver form1 form2 evars] checks entailment form1 |= form2 using
    match1 rules
*)
val entailment : Z3wrapper.solver -> Formula.t -> Formula.t -> variable list
    -> bool

val check_lambda_entailment : Z3wrapper.solver -> Formula.lambda -> Formula.lambda -> int


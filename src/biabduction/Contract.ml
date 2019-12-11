module FExp = Formula.Exp

type formula = Formula.t
type variable = FExp.variable

type t = {
    lhs: formula;
    rhs: formula;
    cvars: variable list; (* list of contract variables -- local within the contract *)
    pvarmap: (variable * variable) list;
    (* the program variables may move to new positions.
       The pvarmap link program variables with contract variables representing the new positions; (old,new) *)
}


let pvarmap_to_string pvarmap =
	CL.Util.list_to_string (fun (x,y) ->
		(FExp.variable_to_string x) ^ "->" ^ (FExp.variable_to_string y) )
		pvarmap


let to_string c =
  "Contract local VARS: " ^ Formula.lvariables_to_string c.cvars ^ "\n"
  ^ "LHS: " ^ Formula.to_string c.lhs ^ "\n"
  ^ "RHS: " ^ Formula.to_string c.rhs ^ "\n"
  ^ "Prog. VARS moves: " ^ pvarmap_to_string c.pvarmap ^ "\n"

let print c = print_string (to_string c)



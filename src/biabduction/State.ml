type variable = Formula.Exp.variable

type t = { 
    miss: Formula.t;
    act: Formula.t;
    lvars: variable list;
}

let empty = {miss = Formula.empty; act = Formula.empty; lvars = []}

let to_string state =
  "EXISTS: " ^ CL.Util.list_to_string string_of_int state.lvars 
  ^ "\nMISS: " ^ Formula.to_string state.miss 
  ^ "\nACTUAL: " ^ Formula.to_string state.act ^ "\n"
  
let print state =
  print_string (to_string state)

let rec simplify_ll gvars evars state = 
  let equiv=Formula.get_varmap state.act.pi in
  match evars with
  | [] -> state
  | a :: rest ->
    let eq_vars=(Formula.get_eq_vars [a] equiv) in
    let notmem l x =
      let eq y= (x=y) in
      not (List.exists eq l)
    in
    let eq_vars_ex = List.filter (notmem gvars) eq_vars in 
    let todo_evars =  List.filter (notmem eq_vars) rest in 
    let act1 = Formula.substitute a eq_vars_ex state.act in
    let miss1 = Formula.substitute a eq_vars_ex state.miss in
    let lvars1 = List.filter (notmem eq_vars_ex) state.lvars in
      simplify_ll gvars todo_evars {miss=miss1; act=act1; lvars=lvars1}

(* NOT FINISHED *)
(* remove redundant existential variables
   -- i.e. if V1 anv V2 are existential variables and state.act contains equality "V1=V2", then V2 is renamed to V1.
*)
let simplify state =
  let mem lst x =
    let eq y= (x=y) in
    (List.exists eq lst )
  in
  let nomem lst x = not (mem lst x) in
  let vars = Formula.join_list_unique (Formula.find_vars state.act) (Formula.find_vars state.miss) in
  let used_lvars = List.filter (mem vars) state.lvars in
  let gvars = List.filter (nomem state.lvars) vars in
  let state0 = {miss=state.miss; act=state.act; lvars=used_lvars} in
  let state1 = simplify_ll gvars used_lvars state0 in
  let miss_new = { Formula.sigma=state1.miss.sigma;
    pi=Formula.remove_redundant_eq state1.miss.pi } in
  let act_new = { Formula.sigma=state1.act.sigma;
    pi=Formula.remove_redundant_eq state1.act.pi } in
  {miss=miss_new; act=act_new; lvars=state1.lvars }

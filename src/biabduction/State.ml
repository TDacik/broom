type variable = Formula.Exp.variable

type t = { 
    miss: Formula.t;
    act: Formula.t;
    lvars: variable list;
}

let empty = {miss = Formula.empty; act = Formula.empty; lvars = []}

let to_string state =
  "EXISTS: " ^ Formula.lvariables_to_string state.lvars
  ^ "\nMISS: " ^ Formula.to_string ~lvars:state.lvars state.miss
  ^ "\nACTUAL: " ^ Formula.to_string ~lvars:state.lvars state.act ^ "\n"
  
let print state =
  print_string (to_string state)

(* substate contains in miss and act only clauses with variables from fixed_vars
   and related variables
   fixed_vars - list of Exp, but expect CVar and Var only *)
let substate fixed_vars state =
	let get_lvar var =
		match var with
		| Formula.Exp.Var v -> if (List.mem v state.lvars) then Some v else None
		| _ -> None
	in
	let rec substate_rec vars s =
		match vars with
		| [] -> empty
		| _ ->
			let (miss_vars,new_miss) = Formula.subformula vars s.miss in
			let (act_vars,new_act) = Formula.subformula vars s.act in
			let new_vars = CL.Util.list_join_unique miss_vars act_vars in
			let all_vars = List.filter_map get_lvar (new_vars @ vars) in
			let tl_s = substate_rec new_vars
				{miss = (Formula.diff s.miss new_miss);
				 act = (Formula.diff s.act new_act);
				 lvars = all_vars} in
			{miss = Formula.disjoint_union new_miss tl_s.miss;
			 act = Formula.disjoint_union new_act tl_s.act;
			 lvars = CL.Util.list_join_unique tl_s.lvars all_vars}
	in
	substate_rec fixed_vars state

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

let simplify state =
  let mem lst x =
    let eq y= (x=y) in
    (List.exists eq lst )
  in
  let nomem lst x = not (mem lst x) in
  let vars = CL.Util.list_join_unique (Formula.find_vars state.act) (Formula.find_vars state.miss) in
  let used_lvars = List.filter (mem vars) state.lvars in
  let gvars = List.filter (nomem state.lvars) vars in
  let state0 = {miss=state.miss; act=state.act; lvars=used_lvars} in
  let state1 = simplify_ll gvars used_lvars state0 in
  let miss_new0 = Formula.remove_useless_conjuncts state1.miss state1.lvars in
  let miss_new = { Formula.sigma=miss_new0.sigma; pi=Formula.remove_redundant_eq miss_new0.pi } in
  (* logical variables used in miss_new can not be removed from act_new by means of remove_useless_conjuncts in order to preserve anchors 
     --- if miss_new contains l1 -- (8)-- >_ and act_new freed(l1) then freed(l1) can not be removed *)
  let lvars_unused_in_miss = List.filter (nomem (Formula.find_vars state.miss)) state1.lvars in
  let act_new0= Formula.remove_useless_conjuncts state1.act lvars_unused_in_miss in
  let act_new = { Formula.sigma=act_new0.sigma;
    pi=Formula.remove_redundant_eq act_new0.pi } in
  {miss=miss_new; act=act_new; lvars=state1.lvars }

open Formula

type state = { 
    miss: Formula.t;  
    act: Formula.t;  
    lvars: int list;
}

let rec simplify_ll gvars evars state = 
	let equiv=get_varmap state.act.pi in
	match evars with
	| [] -> state
	| a :: rest -> 	
		let eq_vars=(get_eq_vars [a] equiv) in
		let notmem l x =
			let eq y= (x=y) in
			not (List.exists eq l)
		in
		let eq_vars_ex = List.filter (notmem gvars) eq_vars in 
		let todo_evars =  List.filter (notmem eq_vars) rest in 
		let act1= substitute a eq_vars_ex state.act in
		let miss1= substitute a eq_vars_ex state.miss in
		let lvars1= List.filter (notmem eq_vars_ex) state.lvars in
			simplify_ll gvars todo_evars {miss=miss1; act=act1; lvars=lvars1}

(* NOT FINISHED *)
let simplify state=
	let mem x =
		let eq y= (x=y) in
		not (List.exists eq state.lvars )
	in
	let vars=join_list_unique (find_vars state.act) (find_vars state.miss) in
	let gvars=List.filter mem vars in
	let state1 = simplify_ll gvars state.lvars state in
	state1


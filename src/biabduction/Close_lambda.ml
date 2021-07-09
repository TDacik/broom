(* Close lambda
   - for each allocate block within lambda add pointsto(s) to fill the whole block (if needed) 
   - the lambda then contains whole blocks only
   - INPUT example: x -(8) -> _ * x+16 - (8) -> _ & base(x)=x
   - OUTPUT example:  x -(8) -> _ * x+8 - (8) -> _ * x+16 - (8) -> _ * x+24 -(len(x)-24)-> _ & base(x)=x 
*)

open Formula
open Z3wrapper
open Z3

let close_lambda lambda =
	print_endline "Closing lambda:";
	print_with_lambda lambda.form;
	print_endline "-------------";
	(* create a fresh solver --  the main one contains asserted "form" but we need to assert unfolded form *)
	let solver=Z3wrapper.config_solver () in
	let ctx=solver.ctx in
	let solv=solver.solv in
	let z3_names=solver.z3_names in
	Solver.add solv (formula_to_solver ctx lambda.form);
	(* get pto from sigmat with equal base *)
	let rec get_block_pto base sigma =
		match sigma with
		| [] -> [],[]
		| Hpointsto (a,b,c)::rest ->
			let query=[Boolean.mk_not ctx (Boolean.mk_eq ctx base (Expr.mk_app ctx z3_names.base [expr_to_solver_only_exp ctx z3_names a])) ] in
			let added,skiped= if (Solver.check solv query)=SATISFIABLE 
				then [],[ Hpointsto (a,b,c) ]
				else [ Hpointsto (a,b,c) ],[]
			in
			let inblock,outblock=(get_block_pto base rest) in
			added @ inblock, skiped @ outblock
		| _::rest -> (* we drop all list segments *)
			get_block_pto base rest
	in
	(* split pointsto in sigma into blocks with equal bases, all list segments are ignored *)
	let rec get_blocks sigma =
		match sigma with
		| [] -> []
		| Hpointsto (a,_,_)::_ -> 
			let base=(Expr.mk_app ctx z3_names.base [expr_to_solver_only_exp ctx z3_names a]) in
			let bl,rest=get_block_pto base sigma in
			bl :: (get_blocks rest)
		| _ :: rest -> get_blocks rest
	in
	let blocks=get_blocks lambda.form.sigma in 
	let rec print_blocks bl =
		match bl with
		| [] -> print_endline "END"
		| first::rest -> print_string "BLOCK:"; print {sigma=first; pi=[]}; print_blocks rest
	in
	print_blocks blocks;
	lambda


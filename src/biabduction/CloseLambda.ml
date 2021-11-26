(* Close lambda
   - for each allocate block within lambda add pointsto(s) to fill the whole
     block (if needed) 
   - the lambda then contains whole blocks only
   - INPUT example: x -(8) -> _ * x+16 -(8)-> _ & base(x)=x
   - OUTPUT example: x -(8) -> _ * x+8 -(8)-> _ * x+16 -(8)-> _ *
                     x+24 -(len(x)-24)-> _ & base(x)=x 
*)

open Formula
open Z3wrapper
open Z3

exception ErrorInLambdaClosing of Config.src_pos

let close_lambda lambda =
	(*print_endline "Closing lambda:";
	print_with_lambda lambda.form;
	print_endline "-------------";*)
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
	(* sort the block od points-to predicates *)
	let order_in_block b1 b2 =
		match b1,b2 with
		| (Hpointsto (a,_,_)), (Hpointsto (b,_,_)) ->
			let query=[BitVector.mk_slt ctx (expr_to_solver_only_exp ctx z3_names a) (expr_to_solver_only_exp ctx z3_names b)] in
			(match (Solver.check solv query) with
			| SATISFIABLE -> -1
			| UNSATISFIABLE -> 1
			| _ -> raise_notrace (ErrorInLambdaClosing __POS__)
			)
		| _ -> raise_notrace (ErrorInLambdaClosing __POS__)
	in
	let sorted_blocks=List.map (List.sort order_in_block) blocks in
	(* close blocks by missing pointsto *)
	let close_block block =
		(* first check that there is no space before the first points-to *)
		let beg=match List.nth block 0 with
			| (Hpointsto (a,_,_)) -> a
			| _ -> raise_notrace (ErrorInLambdaClosing __POS__)
		in
		let base_beg=(Expr.mk_app ctx z3_names.base [expr_to_solver_only_exp ctx z3_names beg]) in
		let query_beg=[Boolean.mk_not ctx 
				(Boolean.mk_eq ctx 
				(expr_to_solver_only_exp ctx z3_names beg) 
				base_beg)]
		in
		let res1= match (Solver.check solv query_beg) with
			| UNSATISFIABLE -> []
			| SATISFIABLE ->
				let size=(Exp.BinOp (Pminus, beg, UnOp ( Base, beg))) in
				let size2=
					match (try_simplify_SL_expr_to_int {ctx=ctx; solv=solv; z3_names=z3_names} {sigma=[]; pi=[]} size) with
					| None -> size
					| Some a -> Exp.Const (Int a)
      				in

				[Hpointsto (UnOp ( Base, beg),size2 ,Undef)]
			| _ -> raise_notrace (ErrorInLambdaClosing __POS__)
		in
		(* check that there is no space between particular pointsto *)
		let check_intermediate index =
			let p1,p2=match (List.nth block index),(List.nth block (index+1)) with
				| (Hpointsto (a,l,_)),(Hpointsto (b,_,_)) ->  (Exp.BinOp (Pplus, a, l)),b
				| _ -> raise_notrace (ErrorInLambdaClosing __POS__)
			in
			let query=[Boolean.mk_not ctx 
				(Boolean.mk_eq ctx 
				(expr_to_solver_only_exp ctx z3_names p1)
				(expr_to_solver_only_exp ctx z3_names p2))]
			in
			match (Solver.check solv query) with
			| SATISFIABLE ->
				let size=(Exp.BinOp (Pminus, p2, p1 )) in
				let size2=
					match (try_simplify_SL_expr_to_int {ctx=ctx; solv=solv; z3_names=z3_names} {sigma=[]; pi=[]} size) with
					| None -> size
					| Some a -> Exp.Const (Int a)
      				in
				[Hpointsto (p1,size2 ,Undef)]
			| UNSATISFIABLE -> []
			| _ -> raise_notrace (ErrorInLambdaClosing __POS__)
		in
		let rec close_intermediate index =
			if index=((List.length block)-1) 
			then []
			else (check_intermediate index)@ close_intermediate (index+1)
		in
		
		(* check that there is no space after the last points-to *)
		let fin=match List.nth block ((List.length block)-1) with
			| (Hpointsto (a,b,_)) -> Exp.BinOp (Pplus, a, b)
			| _ -> raise_notrace (ErrorInLambdaClosing __POS__)
		in
		let query_fin=[Boolean.mk_not ctx 
				(Boolean.mk_eq ctx 
				(BitVector.mk_add ctx base_beg (Expr.mk_app ctx z3_names.len [base_beg]))
				(expr_to_solver_only_exp ctx z3_names fin))] 
				
		in
		let res2= match (Solver.check solv query_fin) with
			| UNSATISFIABLE -> []
			| SATISFIABLE ->
				let size_to_end=(Exp.BinOp (Pminus, UnOp(Len, UnOp(Base,beg)), BinOp(Pminus,fin,UnOp(Base,beg)))) in
				let size_to_end2=
					match (try_simplify_SL_expr_to_int {ctx=ctx; solv=solv; z3_names=z3_names} {sigma=[]; pi=[]} size_to_end) with
					| None -> size_to_end
					| Some a -> Exp.Const (Int a)
      				in
				[Hpointsto (fin,size_to_end2,Undef)]
			| _ -> raise_notrace (ErrorInLambdaClosing __POS__)
		in
		res1@block@(close_intermediate 0)@res2
					
	in
	(* get slseg/dlseg from the original lambda *)
	let rec get_lseg sigma =
		match sigma with
		| [] -> []
		| (Slseg (a,b,c))::rest -> (Slseg (a,b,c)) :: get_lseg rest
		| (Dlseg (a,b,c,d,e)):: rest -> (Dlseg (a,b,c,d,e)) :: get_lseg rest
		| _::rest -> (* we drop pointsto *)
			get_lseg rest
	in


	let closed_blocks=List.map close_block sorted_blocks in
	(*
	let rec print_blocks bl =
		match bl with
		| [] -> print_endline "END"
		| first::rest -> print_string "BLOCK:"; print {sigma=first; pi=[]}; print_blocks rest
	in
	print_blocks closed_blocks;*)
	let res_form={sigma=(List.concat closed_blocks)@(get_lseg lambda.form.sigma); pi=lambda.form.pi} in
	{form=res_form; param=lambda.param}


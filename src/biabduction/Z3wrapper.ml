open Z3
(*open Z3.Symbol*)
(* open Z3.BitVector *)
open Formula


(* width of the bitvector TODO: as a config parameter *)
let bw_width=64

(* The functions base, len, size, onstack, etc in SL are used as uninterpreted functions in z3 *)
type sl_function_names_z3 = {
  base : FuncDecl.func_decl;
  len : FuncDecl.func_decl;
  alloc : FuncDecl.func_decl;
  onstack : FuncDecl.func_decl;
  static : FuncDecl.func_decl;
}

type solver = {
  ctx : Z3.context;
  solv : Z3.Solver.solver;
  z3_names : sl_function_names_z3;
}

let get_sl_functions_z3 ctx =
  {
    base=FuncDecl.mk_func_decl ctx (Symbol.mk_string ctx "base")
      [(BitVector.mk_sort ctx bw_width)] (BitVector.mk_sort ctx bw_width);
    len=FuncDecl.mk_func_decl ctx (Symbol.mk_string ctx "len")
      [(BitVector.mk_sort ctx bw_width)] (BitVector.mk_sort ctx bw_width);
    alloc=FuncDecl.mk_func_decl ctx (Symbol.mk_string ctx "alloc")
      [(BitVector.mk_sort ctx bw_width)] (Boolean.mk_sort ctx);
    onstack=FuncDecl.mk_func_decl ctx (Symbol.mk_string ctx "onstack")
      [(BitVector.mk_sort ctx bw_width)] (Boolean.mk_sort ctx);
    static=FuncDecl.mk_func_decl ctx (Symbol.mk_string ctx "static")
      [(BitVector.mk_sort ctx bw_width)] (Boolean.mk_sort ctx);
  }

let config_solver () =
  let cfg = [("model", "true"); ("proof", "false")] in
  let ctx = (Z3.mk_context cfg) in
  let solv = (Z3.Solver.mk_solver ctx None) in
  let z3_names = get_sl_functions_z3 ctx in
  {ctx = ctx; solv = solv; z3_names = z3_names}

(* Create existential quantifier 
   ctx - Z3context, evars - a list of variables for quantification, form - Z3 expression *)
let create_ex_quantifier ctx evars form =
      match evars with
      | [] -> form
      | ev -> Quantifier.expr_of_quantifier
        (Quantifier.mk_exists_const ctx ev form (Some 1) [] []
        (Some (Symbol.mk_string ctx "Q1")) (Some (Symbol.mk_string ctx "skid1")))

(* Boolean <-> Bitvector conversion *)

let mk_bvtrue ctx = BitVector.mk_numeral ctx "-1" bw_width

let mk_bvfalse ctx = BitVector.mk_numeral ctx "0" bw_width

(* if bool == true then "-1" else "0" *)
let mk_bool2bv ctx z3expr =
  if Boolean.is_true z3expr then (mk_bvtrue ctx)
  else if Boolean.is_false z3expr then (mk_bvfalse ctx)
  else Boolean.mk_ite ctx z3expr (mk_bvtrue ctx) (mk_bvfalse ctx)

(* if bv == "0" then false else true *)
let mk_bv2bool ctx z3expr =
  let eq0 = Boolean.mk_eq ctx z3expr (mk_bvfalse ctx) in
  Boolean.mk_ite ctx eq0 (Boolean.mk_false ctx) (Boolean.mk_true ctx)

(* if bv == "0" then bv else "-1" *)
let mk_binary_bv ctx z3expr =
  let eq0 = Boolean.mk_eq ctx z3expr (mk_bvfalse ctx) in
  Boolean.mk_ite ctx eq0 z3expr (mk_bvtrue ctx)


(* Pure part translation into Z3 solver internal representation *)

exception NoZ3Translation of string

(* check and set, if all operands of boolean experession are in same sort *)
let boolexpr_to_solver ctx mk_expr a b =
  let sort_a = Expr.get_sort a in
  let sort_b = Expr.get_sort b in
  if Sort.equal sort_a sort_b
  then mk_expr ctx a b
  else (match (Boolean.is_bool a),(Boolean.is_bool b) with
    | true,false -> mk_expr ctx (mk_bool2bv ctx a) b
    | false,true -> mk_expr ctx a (mk_bool2bv ctx b)
    | _,_ -> raise (NoZ3Translation "Unsupported Boolean expression in Z3")
  )

(* for binary logical operators *)
let logicexpr_to_solver ctx mk_boolexpr mk_bvexpr a b =
  match (Boolean.is_bool a),(Boolean.is_bool b) with
  | true,false -> mk_bvexpr ctx (mk_bool2bv ctx a) (mk_binary_bv ctx b)
  | false,true -> mk_bvexpr ctx (mk_binary_bv ctx a) (mk_bool2bv ctx b)
  | false,false -> mk_bvexpr ctx (mk_binary_bv ctx a) (mk_binary_bv ctx b)
  | true,true -> mk_boolexpr ctx a b

let const_to_solver ctx c =
  match c with
  | Exp.Ptr a -> BitVector.mk_numeral ctx (string_of_int a) bw_width
  | Exp.Int a -> BitVector.mk_numeral ctx (Int64.to_string a) bw_width
  | Exp.Bool a -> Boolean.mk_val ctx a
  | Exp.String _ -> raise (NoZ3Translation "Can't translate String expression to Z3")
  | Exp.Float _ -> raise (NoZ3Translation "Can't translate Float expression to Z3")
  (*| Exp.String a -> a *)
  (* | Exp.Float a -> Real.mk_numeral_i ctx a *)


(* the function returns tuple (z3exp,exundef), where
    z3exp is an expression in Z3 api and 
    exundef are newly created existential variables --- UNDEF is translated to \exists x.  x *)

let rec expr_to_solver ctx func expr =
  match expr with
  | Exp.Var a -> 
  	(Expr.mk_const ctx (Symbol.mk_string ctx (string_of_int a)) (BitVector.mk_sort ctx bw_width)), []
  | Exp.CVar _ -> raise (NoZ3Translation "Contract variable shouldn't be in Z3")
  | Exp.Const a -> (const_to_solver ctx a), []
  | Exp.UnOp (op,a) ->
    ( match op with
      | Base -> let exp1,exists1=(expr_to_solver ctx func a) in
      		(Expr.mk_app ctx func.base [exp1]), exists1
      | Len ->  let exp1,exists1=(expr_to_solver ctx func a) in
      		(Expr.mk_app ctx func.len [exp1]), exists1
      | Freed -> let exp1,exists1=(expr_to_solver ctx func a) in
      		(Boolean.mk_and ctx [ 
      		(Boolean.mk_not ctx (Expr.mk_app ctx func.alloc [exp1]));
		(Boolean.mk_not ctx (Expr.mk_app ctx func.onstack [exp1]));
		(Boolean.mk_not ctx (Expr.mk_app ctx func.static [exp1]));
		(Boolean.mk_eq ctx exp1 (Expr.mk_app ctx func.base [exp1]));
      		(Boolean.mk_not ctx (Boolean.mk_eq ctx exp1 (BitVector.mk_numeral ctx "0" bw_width)))
		]), exists1

      | Invalid -> let exp1,exists1=(expr_to_solver ctx func a) in
      		(Boolean.mk_and ctx [ 
      		(Boolean.mk_not ctx (Expr.mk_app ctx func.alloc [exp1]));
		(Expr.mk_app ctx func.onstack [exp1]);
		]), exists1
      | BVnot -> let exp1,exists1=(expr_to_solver ctx func a) in
      		(BitVector.mk_not ctx exp1), exists1
      | Pnot -> let exp1,exists1=(expr_to_solver ctx func a) in
      		(Boolean.mk_not ctx exp1),exists1
      | Puminus -> let exp1,exists1=(expr_to_solver ctx func a) in
      		(BitVector.mk_neg ctx exp1), exists1
      (* | _ -> raise (NoZ3Translation "Unsupported unary operator in Z3") *)
    )
  | Exp.BinOp (op,a,b) ->
    ( match op with
      | Stack  -> let exp1,exists1=(expr_to_solver ctx func a) in
      		(Boolean.mk_and ctx [
			(Expr.mk_app ctx func.onstack [exp1]);
			(Expr.mk_app ctx func.onstack [(Expr.mk_app ctx func.base [exp1])]);
			(Boolean.mk_not ctx (Expr.mk_app ctx func.static [(Expr.mk_app ctx func.base [exp1])]));
		]), exists1
      |  Static -> let exp1,exists1=(expr_to_solver ctx func a) in
      		(Boolean.mk_and ctx [
			(Expr.mk_app ctx func.static [exp1]);
			(Expr.mk_app ctx func.static [(Expr.mk_app ctx func.base [exp1])]);
			(Boolean.mk_not ctx (Expr.mk_app ctx func.onstack [(Expr.mk_app ctx func.base [exp1])]));
		]), exists1
      | Peq -> let exp1,exists1=(expr_to_solver ctx func a) in
      		let exp2,exists2=(expr_to_solver ctx func b) in
      		(boolexpr_to_solver ctx Boolean.mk_eq exp1 exp2), (exists1@exists2)
      | Pneq -> let exp1,exists1=(expr_to_solver ctx func a) in
      		let exp2,exists2=(expr_to_solver ctx func b) in
        	let mk_neq ctx a b = Boolean.mk_not ctx (Boolean.mk_eq ctx a b) in
        	(boolexpr_to_solver ctx mk_neq exp1 exp2), (exists1@exists2)
      | Pless -> let exp1,exists1=(expr_to_solver ctx func a) in
      		let exp2,exists2=(expr_to_solver ctx func b) in 
      		(BitVector.mk_slt ctx exp1 exp2), (exists1@exists2) 
      | Plesseq -> let exp1,exists1=(expr_to_solver ctx func a) in
      		let exp2,exists2=(expr_to_solver ctx func b) in 
      		(BitVector.mk_sle ctx exp1 exp2), (exists1@exists2)
      | Pand -> let exp1,exists1=(expr_to_solver ctx func a) in
      		let exp2,exists2=(expr_to_solver ctx func b) in 
        	let mk_and_two ctx a b = Boolean.mk_and ctx [a;b] in
        	(logicexpr_to_solver ctx mk_and_two BitVector.mk_add exp1 exp2), (exists1@exists2)
      | Por -> let exp1,exists1=(expr_to_solver ctx func a) in
      		let exp2,exists2=(expr_to_solver ctx func b) in
        	let mk_or_two ctx a b = Boolean.mk_or ctx [a;b] in
        	(logicexpr_to_solver ctx mk_or_two BitVector.mk_or exp1 exp2), (exists1@exists2)
      | Pxor -> let exp1,exists1=(expr_to_solver ctx func a) in
      		let exp2,exists2=(expr_to_solver ctx func b) in
        	(logicexpr_to_solver ctx Boolean.mk_xor BitVector.mk_xor exp1 exp2),  (exists1@exists2)
      | Pplus -> let exp1,exists1=(expr_to_solver ctx func a) in
      		let exp2,exists2=(expr_to_solver ctx func b) in
      		(BitVector.mk_add ctx exp1 exp2), (exists1@exists2)
      | Pminus ->  let exp1,exists1=(expr_to_solver ctx func a) in
      		let exp2,exists2=(expr_to_solver ctx func b) in
      		(BitVector.mk_sub ctx  exp1 exp2), (exists1@exists2)
      | Pmult ->  let exp1,exists1=(expr_to_solver ctx func a) in
      		let exp2,exists2=(expr_to_solver ctx func b) in
      		(BitVector.mk_mul ctx exp1 exp2), (exists1@exists2)
      | Pdiv ->  let exp1,exists1=(expr_to_solver ctx func a) in
      		let exp2,exists2=(expr_to_solver ctx func b) in
     		(BitVector.mk_sdiv ctx exp1 exp2), (exists1@exists2)
      | Pmod ->  let exp1,exists1=(expr_to_solver ctx func a) in
      		let exp2,exists2=(expr_to_solver ctx func b) in
      		(BitVector.mk_smod ctx exp1 exp2), (exists1@exists2)
      | BVand -> let exp1,exists1=(expr_to_solver ctx func a) in
      		let exp2,exists2=(expr_to_solver ctx func b) in
      		(BitVector.mk_and ctx exp1 exp2), (exists1@exists2)
      | BVor -> let exp1,exists1=(expr_to_solver ctx func a) in
      		let exp2,exists2=(expr_to_solver ctx func b) in
      		(BitVector.mk_or ctx exp1 exp2), (exists1@exists2)
      | BVxor ->  let exp1,exists1=(expr_to_solver ctx func a) in
      		let exp2,exists2=(expr_to_solver ctx func b) in
      		(BitVector.mk_xor ctx exp1 exp2), (exists1@exists2)
      | BVlshift -> let exp1,exists1=(expr_to_solver ctx func a) in
      		let exp2,exists2=(expr_to_solver ctx func b) in
      		(BitVector.mk_shl ctx exp1 exp2),  (exists1@exists2)
      | BVrshift ->  let exp1,exists1=(expr_to_solver ctx func a) in
      		let exp2,exists2=(expr_to_solver ctx func b) in
      		(BitVector.mk_ashr ctx exp1 exp2), (exists1@exists2)
      | BVlrotate -> let exp1,exists1=(expr_to_solver ctx func a) in
      		let exp2,exists2=(expr_to_solver ctx func b) in
      		(BitVector.mk_ext_rotate_left ctx exp1 exp2), (exists1@exists2)
      | BVrrotate -> let exp1,exists1=(expr_to_solver ctx func a) in
      		let exp2,exists2=(expr_to_solver ctx func b) in
      		(BitVector.mk_ext_rotate_right ctx exp1 exp2), (exists1@exists2)
      (* | _ -> raise (NoZ3Translation "Unsupported binary operator in Z3") *)
    )
  | Exp.Void ->  (BitVector.mk_numeral ctx "-1" bw_width ), []
  | Exp.Undef -> let undefvar=Expr.mk_fresh_const ctx "UNDEF" (BitVector.mk_sort ctx bw_width) in
  		undefvar, [undefvar]

let expr_to_solver_only_exp ctx func expr =
	let x,_=expr_to_solver ctx func expr in
	x

(* create conditions to guarantee SL * validity ... *)
(*  " a-> ... => alloc(base a)  " *)
(*  " x-> ... * y -> ... => x!=y "/\" [base(x)= base(y) => y + size_y<=x "\/" x+size_x<=y] " *)

let (*rec*) spatial_pred_to_solver ctx sp_pred1 rest_preds func =
  let alloc node=(expr_to_solver ctx func node) in
  let base_eq x y =
    Boolean.mk_eq ctx
      (Expr.mk_app ctx func.base [x])
      (Expr.mk_app ctx func.base [y])
  in
  match sp_pred1 with
  | Hpointsto (a, size, _) -> (
    (* Create "local" constraints for a single points-to *)
    (* local_c[123] = alloc(base a)
        /\ base(a) = base(base(a))
        /\ len(a) >=size 
        /\ a>0 
        /\ base(a)<=a 
        /\ a<=a+size_of_field_a --- this guarantee no overflow of bitvector*)
    let x,exundef1=alloc a in
    let local_c1= Expr.mk_app ctx func.alloc [Expr.mk_app ctx func.base [x]] in
    let local_c2= Boolean.mk_eq ctx
        (Expr.mk_app ctx func.base [x])
        (Expr.mk_app ctx func.base [(Expr.mk_app ctx func.base [x])]) in
    let size_z3,exundef2=(expr_to_solver ctx func size) in
    let local_c3 = BitVector.mk_sge ctx (Expr.mk_app ctx func.len [x]) size_z3 in
    let local_c4 = BitVector.mk_sgt ctx x (BitVector.mk_numeral ctx "0" bw_width) in
    let local_c5 = BitVector.mk_sle ctx (Expr.mk_app ctx func.base [x]) x in
    let local_c6 = BitVector.mk_sle ctx x (BitVector.mk_add ctx x size_z3) in
      
    (* Create constrains for two space predicates *)
    (*  dist_fields: x!=y /\ [base(x)= base(y) => y + size_y<=x \/ x+size_x<=y] *)
    (* fit_len: x<=y<x+len(x) \/ y<=x<y+len(y) => base(x) = base(y) *)
    (*  fix_len: x!=y /\ [base(x)= base(y) => x+len(x)=y+len(y)] *)
    let no_overlap x size_x y size_y=
      Boolean.mk_or ctx
      [(BitVector.mk_sle ctx (BitVector.mk_add ctx x size_x ) y);
      (BitVector.mk_sle ctx (BitVector.mk_add ctx y size_y ) x)]
    in
    let dist_fields x size_x y size_y = Boolean.mk_implies ctx (base_eq x y) (no_overlap x size_x y size_y) in
    let fit_len x y = Boolean.mk_implies ctx 
      (Boolean.mk_or ctx [
        Boolean.mk_and ctx [
          BitVector.mk_sle ctx x y;
          BitVector.mk_slt ctx y
            (BitVector.mk_add ctx x (Expr.mk_app ctx func.len [x]))
        ];
        Boolean.mk_and ctx [
          BitVector.mk_sle ctx y x;
          BitVector.mk_slt ctx x
            (BitVector.mk_add ctx y (Expr.mk_app ctx func.len [y]))
        ]
      ])
      (base_eq x y)
    in
    let fix_len x y = Boolean.mk_implies ctx (base_eq x y) 
		(Boolean.mk_eq ctx
			(BitVector.mk_add ctx x (Expr.mk_app ctx func.len [x]))
			(BitVector.mk_add ctx y (Expr.mk_app ctx func.len [y]))
		) 
    in
    let two_sp_preds_c al sp_rule = 
      match sp_rule with
      | Hpointsto (aa, size_aa, _) ->(* create a nonequality al != x, where x is the allocated node in sp_rule *)
        let alloc_aa,ex1 = alloc aa in
	let size_z3,ex2=(expr_to_solver ctx func size) in
	let size_aa_z3,ex3=(expr_to_solver ctx func size_aa) in
	let exundef=ex1@ex2@ex3 in
        (Boolean.mk_and ctx
        	[(Boolean.mk_not ctx (Boolean.mk_eq ctx al alloc_aa));
	        (dist_fields al size_z3 alloc_aa size_aa_z3);
        	(fit_len al alloc_aa);
		(fix_len al alloc_aa)]), exundef
      | Slseg (aa,bb,_) -> (* base(al) != base(aa) or Slseq is empty aa=bb *)
        let alloc_aa,ex1 = alloc aa in
	let alloc_bb,ex2 = alloc bb in
	let exundef=ex1@ex2 in
        Boolean.mk_or ctx
        	[ Boolean.mk_not ctx (base_eq al alloc_aa);
        	Boolean.mk_eq ctx alloc_aa alloc_bb ], exundef
    in
    let rec create_noneq to_parse =
      match to_parse with
      | first:: rest -> 
      		let expr,exundef=(two_sp_preds_c x first) in
		let rest_expr, rest_exundef = create_noneq rest in
		expr:: rest_expr, exundef @ rest_exundef
      | [] -> [],[]
    in
    let noneq,exundef3=create_noneq rest_preds in
    ((Boolean.mk_and ctx [ local_c1; local_c2; local_c3; local_c4; local_c5; local_c6 ]) :: noneq), (exundef1@exundef2@exundef3)
    )
  | Slseg (a,b,_) ->
    let x,exundef1=alloc a in
    let y,exundef2=alloc b in
    (* alloc base(x) or x=y 
       base(x)=base(base(x))
       x>=0 --- x can be 0 in the case of x=y=null *)
    let c1 = Boolean.mk_or ctx
      [ Expr.mk_app ctx func.alloc [Expr.mk_app ctx func.base [x]];
      Boolean.mk_eq ctx x y]  in
    let c2= Boolean.mk_eq ctx
        (Expr.mk_app ctx func.base [x])
        (Expr.mk_app ctx func.base [(Expr.mk_app ctx func.base [x])]) in
    let c3 = BitVector.mk_sge ctx x (BitVector.mk_numeral ctx "0" bw_width) in
    let two_sp_preds_c al dst sp_rule =
      match sp_rule with
      | Hpointsto (aa, _, _) -> (* base(al) != base(aa) or Slseq is empty al=dst *)
	let alloc_aa,exu1=alloc aa in
        Boolean.mk_or ctx
        	[ Boolean.mk_not ctx (base_eq al alloc_aa );
        	Boolean.mk_eq ctx al dst ],exu1
      | Slseg (aa,bb,_) ->(* base(al) != base(aa) or one of the Slseqs is empty al=dst \/ aa=bb *)
	let alloc_aa,exu1=alloc aa in
	let alloc_bb,exu2=alloc bb in
        Boolean.mk_or ctx
        	[ Boolean.mk_not ctx (base_eq al alloc_aa );
        	Boolean.mk_eq ctx al dst;
        	Boolean.mk_eq ctx alloc_aa alloc_bb ], (exu1@exu2)

    in
    let rec sp_constraints to_parse =
      match to_parse with
        | first:: rest -> 
		let exp,exundef=(two_sp_preds_c x y first) in
		let rest_exp,rest_exundef = sp_constraints rest in
		exp::rest_exp, exundef@rest_exundef
        | [] -> [],[]
    in
    let sp_constr,exundef3 = (sp_constraints rest_preds) in
    ([c1;c2;c3] @ sp_constr), (exundef1@exundef2@exundef3)

(* Creation of the Z3 formulae for a SL formulae *)

let rec pi_to_solver ctx names_z3 pi quantify_undef =
  match pi with
  | [] -> []
  | first::rest -> 
  	let expr,exundefs=(expr_to_solver ctx names_z3 first) in
  	let rest_expr= (pi_to_solver ctx names_z3 rest quantify_undef) in
	let expr_fin =
		if quantify_undef 
		then (create_ex_quantifier ctx exundefs expr)
		else expr
	in
	expr_fin::rest_expr

let rec sigma_to_solver ctx names_z3 sigma quantify_undef =
  match sigma with
  | [] -> []
  | first::rest -> 
  	let sp_pred_z3,exundefs=(spatial_pred_to_solver ctx first rest names_z3) in
	let  sp_pred_z3_fin=
		if quantify_undef 
		then [create_ex_quantifier ctx exundefs (Boolean.mk_and ctx sp_pred_z3)]
		else sp_pred_z3
	in
  	List.append sp_pred_z3_fin (sigma_to_solver ctx names_z3 rest quantify_undef)

let rec formula_to_string exprs =
  match exprs with
  | [] -> ""
  | expr::tl -> let sort = Expr.get_sort expr in
    "SORT:"^(Sort.to_string sort)^"~~~"^
    (Expr.to_string expr)^"\n"^
    (formula_to_string tl)

let formula_to_solver ctx form =
  let names_z3=get_sl_functions_z3 ctx in
  let pi= pi_to_solver ctx names_z3 form.pi false in
  let sigma= sigma_to_solver ctx names_z3 form.sigma false in
  let null_not_alloc=Boolean.mk_not ctx (Expr.mk_app ctx names_z3.alloc [BitVector.mk_numeral ctx "0" bw_width]) in
  let base0=Boolean.mk_eq ctx
    (BitVector.mk_numeral ctx "0" bw_width)
    (Expr.mk_app ctx names_z3.base [BitVector.mk_numeral ctx "0" bw_width]) in
  pi @ sigma @ [null_not_alloc; base0]

(* for each UNDEF in the formula form, an fresh Z3 variable is created. 
   This function add an existential quantifier for each such a variable. 
   It is needed, when the formula is being placed on the RHS of an implication. 
   When you call only formula_to_solver, a valid implication with UNDEFs can be evaluated as invalid. *)
let formula_to_solver_with_quantified_undefs ctx form =
  let names_z3=get_sl_functions_z3 ctx in
  let pi= pi_to_solver ctx names_z3 form.pi true in
  let sigma= sigma_to_solver ctx names_z3 form.sigma true in
  let null_not_alloc=Boolean.mk_not ctx (Expr.mk_app ctx names_z3.alloc [BitVector.mk_numeral ctx "0" bw_width]) in
  let base0=Boolean.mk_eq ctx
    (BitVector.mk_numeral ctx "0" bw_width)
    (Expr.mk_app ctx names_z3.base [BitVector.mk_numeral ctx "0" bw_width]) in
  pi @ sigma @ [null_not_alloc; base0]

(* check the lambda within the Slseq predicates,
   returns **true** iff the lambda satisfy the basic properties *)
let rec check_sp_predicate ctx solv pred =
  let z3_names=get_sl_functions_z3 ctx in
  match pred with
  | Slseg(_,_,lambda) ->
    (* basic checks, there must be two parameters, which are different *)
    if not ((List.length lambda.param) = 2) ||
      (List.nth lambda.param 0) = (List.nth lambda.param 1) then false
    else
      let lambda_z3=formula_to_solver ctx lambda.form in
      let x,_=expr_to_solver ctx z3_names (Exp.Var (List.nth lambda.param 0)) in
      let y,_=expr_to_solver ctx z3_names (Exp.Var (List.nth lambda.param 1)) in
      let not_alloc_base_x = Boolean.mk_not ctx
        (Expr.mk_app ctx z3_names.alloc [Expr.mk_app ctx z3_names.base [x]]) in
      let not_alloc_base_y = Boolean.mk_not ctx
        (Expr.mk_app ctx z3_names.alloc [Expr.mk_app ctx z3_names.base [y]]) in
      (* Check that 1: labda /\ not(alloc(y) is SAT and 2: lambda => alloc(x) *)
      (Solver.check solv (not_alloc_base_y::lambda_z3))=SATISFIABLE &&
      (Solver.check solv (not_alloc_base_x::lambda_z3))=UNSATISFIABLE &&
      (check_all_lambdas ctx solv lambda.form.sigma)
  | _ -> true

and check_all_lambdas ctx solv sigma =
  match sigma with
  | [] -> true
  | first::rest -> (check_sp_predicate ctx solv first) && (check_all_lambdas ctx solv rest)


(* Experiments *)

(*
let cfg = [("model", "true"); ("proof", "false")]
let ctx = (mk_context cfg)

open Solver
let z3_form1=formula_to_solver ctx form1

let solv = (mk_solver ctx None)
check solv z3_form1

------------------------------------
let form5=
  let lambda= {param=[1;2] ;form={
      sigma = [ Hpointsto (Var 1, 8, Var 2); Hpointsto (Var 2, 8, Var 3) ]; pi=[] }}
  in
  {
          sigma = [ Hpointsto (Var 1,8, Var 2); Slseg (Var 3, Var 4, lambda) ];
      pi = [ BinOp ( Peq, Var 1, UnOp ( Base, Var 1));
          BinOp ( Peq, Var 1, UnOp ( Base, Var 3));
            BinOp ( Peq, UnOp ( Len, Var 1), Const (Int 8));
            BinOp ( Peq, Var 1, Var 2332 );
            BinOp ( Peq, Var 2, Const (Ptr 0)) ]
  }

check_all_lambdas ctx solv form4.sigma;;
check_all_lambdas ctx solv form5.sigma;;

*)

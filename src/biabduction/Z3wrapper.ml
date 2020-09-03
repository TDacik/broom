open Z3
(*open Z3.Symbol*)
(* open Z3.BitVector *)
open Formula


(* width of the bitvector TODO: as a config parameter *)
let bw_width=64

(* The functions base, len, size, etc in SL are used as uninterpreted functions in z3 *)
type sl_function_names_z3 = {
  base : FuncDecl.func_decl;
  len : FuncDecl.func_decl;
  alloc : FuncDecl.func_decl;
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
  }

let config_solver () =
  let cfg = [("model", "true"); ("proof", "false")] in
  let ctx = (Z3.mk_context cfg) in
  let solv = (Z3.Solver.mk_solver ctx None) in
  let z3_names = get_sl_functions_z3 ctx in
  {ctx = ctx; solv = solv; z3_names = z3_names}

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


let rec expr_to_solver ctx func expr =
  match expr with
  | Exp.Var a -> Expr.mk_const ctx (Symbol.mk_string ctx (string_of_int a)) (BitVector.mk_sort ctx bw_width)
  | Exp.CVar _ -> raise (NoZ3Translation "Contract variable shouldn't be in Z3")
  | Exp.Const a -> const_to_solver ctx a
  | Exp.UnOp (op,a) ->
    ( match op with
      | Base -> Expr.mk_app ctx func.base [(expr_to_solver ctx func a)]
      | Len ->  Expr.mk_app ctx func.len [(expr_to_solver ctx func a)]
      | Freed -> Boolean.mk_and ctx [ 
      		(Boolean.mk_not ctx (Expr.mk_app ctx func.alloc [(expr_to_solver ctx func a)]));
      		(Boolean.mk_not ctx (Boolean.mk_eq ctx (expr_to_solver ctx func a) (BitVector.mk_numeral ctx "0" bw_width)))
		]
      | BVnot -> BitVector.mk_not ctx (expr_to_solver ctx func a)
      | Pnot -> Boolean.mk_not ctx (expr_to_solver ctx func a)
      | Puminus -> BitVector.mk_neg ctx (expr_to_solver ctx func a)
      (* | _ -> raise (NoZ3Translation "Unsupported unary operator in Z3") *)
    )
  | Exp.BinOp (op,a,b) ->
    ( match op with
      | Peq -> boolexpr_to_solver ctx Boolean.mk_eq (expr_to_solver ctx func a) (expr_to_solver ctx func b)
      | Pneq ->
        let mk_neq ctx a b = Boolean.mk_not ctx (Boolean.mk_eq ctx a b) in
        boolexpr_to_solver ctx mk_neq (expr_to_solver ctx func a) (expr_to_solver ctx func b)
      | Pless ->  BitVector.mk_slt ctx (expr_to_solver ctx func a) (expr_to_solver ctx func b)
      | Plesseq -> BitVector.mk_sle ctx (expr_to_solver ctx func a) (expr_to_solver ctx func b)
      | Pand ->
        let mk_and_two ctx a b = Boolean.mk_and ctx [a;b] in
        logicexpr_to_solver ctx mk_and_two BitVector.mk_add
          (expr_to_solver ctx func a) (expr_to_solver ctx func b)
      | Por ->
        let mk_or_two ctx a b = Boolean.mk_or ctx [a;b] in
        logicexpr_to_solver ctx mk_or_two BitVector.mk_or
          (expr_to_solver ctx func a) (expr_to_solver ctx func b)
      | Pxor ->
        logicexpr_to_solver ctx Boolean.mk_xor BitVector.mk_xor
          (expr_to_solver ctx func a) (expr_to_solver ctx func b)
      | Pplus -> BitVector.mk_add ctx  (expr_to_solver ctx func a) (expr_to_solver ctx func b) 
      | Pminus -> BitVector.mk_sub ctx  (expr_to_solver ctx func a) (expr_to_solver ctx func b) 
      | Pmult -> BitVector.mk_mul ctx (expr_to_solver ctx func a) (expr_to_solver ctx func b)
      | Pdiv -> BitVector.mk_sdiv ctx (expr_to_solver ctx func a) (expr_to_solver ctx func b)
      | Pmod -> BitVector.mk_smod ctx (expr_to_solver ctx func a) (expr_to_solver ctx func b)
      | BVand -> BitVector.mk_and ctx (expr_to_solver ctx func a) (expr_to_solver ctx func b)
      | BVor -> BitVector.mk_or ctx (expr_to_solver ctx func a) (expr_to_solver ctx func b)
      | BVxor -> BitVector.mk_xor ctx (expr_to_solver ctx func a) (expr_to_solver ctx func b)
      | BVlshift -> BitVector.mk_shl ctx (expr_to_solver ctx func a) (expr_to_solver ctx func b)
      | BVrshift -> BitVector.mk_ashr ctx (expr_to_solver ctx func a) (expr_to_solver ctx func b)
      | BVlrotate -> BitVector.mk_ext_rotate_left ctx (expr_to_solver ctx func a) (expr_to_solver ctx func b)
      | BVrrotate -> BitVector.mk_ext_rotate_right ctx (expr_to_solver ctx func a) (expr_to_solver ctx func b)
      (* | _ -> raise (NoZ3Translation "Unsupported binary operator in Z3") *)
    )
  | Exp.Void ->  BitVector.mk_numeral ctx "-1" bw_width 
  | Exp.Undef -> Expr.mk_fresh_const ctx "UNDEF" (BitVector.mk_sort ctx bw_width)


(* create conditions to guarantee SL * validity ... *)
(*  " a-> ... => alloc(base a)  " *)
(*  " x-> ... * y -> ... => x!=y "/\" [base(x)= base(y) => y + size_y<=x "\/" x+size_x<=y] " *)

let (*rec*) spatial_pred_to_solver ctx sp_pred1 rest_preds func =
  let alloc x=(expr_to_solver ctx func x) in
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
    let x=alloc a in
    let local_c1= Expr.mk_app ctx func.alloc [Expr.mk_app ctx func.base [x]] in
    let local_c2= Boolean.mk_eq ctx
        (Expr.mk_app ctx func.base [x])
        (Expr.mk_app ctx func.base [(Expr.mk_app ctx func.base [x])]) in
    let local_c3 = BitVector.mk_sge ctx
      (Expr.mk_app ctx func.len [x])
      (expr_to_solver ctx func size)
    in
    let local_c4 = BitVector.mk_sgt ctx x (BitVector.mk_numeral ctx "0" bw_width) in
    let local_c5 = BitVector.mk_sle ctx (Expr.mk_app ctx func.base [x]) x in
    let local_c6 = BitVector.mk_sle ctx x (BitVector.mk_add ctx x (expr_to_solver ctx func size) ) in
      
    (* Create constrains for two space predicates *)
    (*  dist_fields: x!=y /\ [base(x)= base(y) => y + size_y<=x \/ x+size_x<=y] *)
    (* fit_len: x<=y<x+len(x) \/ y<=x<y+len(y) => base(x) = base(y) *)
    (*  fix_len: x!=y /\ [base(x)= base(y) => x+len(x)=y+len(y)] *)
    let no_overlap x size_x y size_y=
      Boolean.mk_or ctx
      [(BitVector.mk_sle ctx (BitVector.mk_add ctx x (expr_to_solver ctx func size_x) ) y);
      (BitVector.mk_sle ctx (BitVector.mk_add ctx y (expr_to_solver ctx func size_y) ) x)]
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
        Boolean.mk_and ctx
        [(Boolean.mk_not ctx (Boolean.mk_eq ctx al (alloc aa)));
        (dist_fields al size (alloc aa) size_aa);
        (fit_len al (alloc aa));
	(fix_len al (alloc aa))]
      | Slseg (aa,bb,_) -> (* base(al) != base(aa) or Slseq is empty aa=bb *)
        Boolean.mk_or ctx
        [ Boolean.mk_not ctx (base_eq al (alloc aa));
        Boolean.mk_eq ctx (alloc aa) (alloc bb) ]
    in
    let rec create_noneq to_parse =
      match to_parse with
      | first:: rest -> (two_sp_preds_c x first) :: create_noneq rest
      | [] -> []
    in
    (Boolean.mk_and ctx [ local_c1; local_c2; local_c3; local_c4; local_c5; local_c6 ]) :: create_noneq rest_preds)
  | Slseg (a,b,_) ->
    let x=alloc a in
    let y=alloc b in
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
        Boolean.mk_or ctx
        [ Boolean.mk_not ctx (base_eq al (alloc aa) );
        Boolean.mk_eq ctx al dst ]
      | Slseg (aa,bb,_) ->(* base(al) != base(aa) or one of the Slseqs is empty al=dst \/ aa=bb *)
        Boolean.mk_or ctx
        [ Boolean.mk_not ctx (base_eq al (alloc aa) );
        Boolean.mk_eq ctx al dst;
        Boolean.mk_eq ctx (alloc aa) (alloc bb) ]

    in
    let rec sp_constraints to_parse =
      match to_parse with
        | first:: rest -> (two_sp_preds_c x y first) :: sp_constraints rest
        | [] -> []
    in
    [c1;c2;c3] @ (sp_constraints rest_preds)

(* Creation of the Z3 formulae for a SL formulae *)

let rec pi_to_solver ctx names_z3 pi =
  match pi with
  | [] -> []
  | first::rest -> (expr_to_solver ctx names_z3 first) :: (pi_to_solver ctx names_z3 rest)

let rec sigma_to_solver ctx names_z3 sigma =
  match sigma with
  | [] -> []
  | first::rest -> List.append (spatial_pred_to_solver ctx first rest names_z3) (sigma_to_solver ctx names_z3 rest)

let rec formula_to_string exprs =
  match exprs with
  | [] -> ""
  | expr::tl -> let sort = Expr.get_sort expr in
    "SORT:"^(Sort.to_string sort)^"~~~"^
    (Expr.to_string expr)^"\n"^
    (formula_to_string tl)

let formula_to_solver ctx form =
  let names_z3=get_sl_functions_z3 ctx in
  let pi= pi_to_solver ctx names_z3 form.pi in
  let sigma= sigma_to_solver ctx names_z3 form.sigma in
  let null_not_alloc=Boolean.mk_not ctx (Expr.mk_app ctx names_z3.alloc [BitVector.mk_numeral ctx "0" bw_width]) in
  let base0=Boolean.mk_eq ctx
    (BitVector.mk_numeral ctx "0" bw_width)
    (Expr.mk_app ctx names_z3.base [BitVector.mk_numeral ctx "0" bw_width]) in
  pi @ sigma @ [null_not_alloc; base0]
  (* pi @ sigma @ global_constr *)


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
      let x=expr_to_solver ctx z3_names (Exp.Var (List.nth lambda.param 0)) in
      let y=expr_to_solver ctx z3_names (Exp.Var (List.nth lambda.param 1)) in
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

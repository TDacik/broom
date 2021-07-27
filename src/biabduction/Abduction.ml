(* in Utop use
  #mod_use "Formula.ml"
     #require "z3"
  #mod_use "Z3wrapper.ml"
*)

open Formula
open Z3
open Z3wrapper

type variable = Formula.Exp.variable

exception TempExceptionBeforeApiCleanup of string
exception NoApplicableRule

(** result of the rule application
    form1 * form2 * M * added_local_vars
    or Fail
**)
type split_record =
  | Record of Formula.heap_pred * Formula.t * Formula.pi
  | NoRecord

type res =
  | Apply of Formula.t * Formula.t * Formula.t * variable list * split_record
  | Fail

let to_slseg_unsafe hpred = match hpred with
  | Hpointsto _ | Dlseg _ -> raise (Invalid_argument "to_slseg_unsafe: Received points-to/dll instead of list")
  | Slseg (a,b,l) -> (a,b,l)

let to_hpointsto_unsafe hpred = match hpred with
  | Slseg _ | Dlseg _ -> raise (Invalid_argument "to_hpointsto_unsafe: Received list instead of points-to")
  | Hpointsto (a,l,b) -> (a,l,b)
let to_dlseg_unsafe hpred = match hpred with
  | Hpointsto _ | Slseg _ -> raise (Invalid_argument "to_dlseg_unsafe: Received points-to instead of dll list")
  | Dlseg (a,b,c,d,l) -> (a,b,c,d,l)

(**** LEARN - pointsto ****)

(* let x be: form2.sigma[i2]=x->_
  we know that x!= y for all y->_ \in form1.sigma
  now find a z->_ in form1.sigma such that base(z) = base(x) is valid *)
let rec find_z ctx solv z3_names form1 z form2 i2 =
  if (List.length form1.sigma) <= z
    then -1
  else
  let (a, _, _) = to_hpointsto_unsafe (List.nth form2.sigma i2) in (* SIZE missing *) (* RHS can be Hpointsto only *)
  let rhs = expr_to_solver_only_exp ctx z3_names a in (* Existential quantification of undef is probably not needed. *)
  match (List.nth form1.sigma z) with
    | Slseg _ | Dlseg _ -> (find_z ctx solv z3_names form1 (z+1) form2 i2)
    | Hpointsto (a,_, _) ->
    let lhs= (expr_to_solver_only_exp ctx z3_names a) in (* Existential quantification is probably not needed. *)(* SIZE missing *)
    let query1= [ Boolean.mk_not ctx (
      Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [lhs]) (Expr.mk_app ctx z3_names.base [rhs]));
      (Boolean.mk_not ctx (Boolean.mk_eq ctx lhs rhs))
      ]
    in
    if ((Solver.check solv query1)=UNSATISFIABLE) then z
    else find_z ctx solv z3_names form1 (z+1) form2 i2

(* check whether we can apply learn on the form2.sigma[i2].
   The result is -1: imposible
        0...k: the index of "z" (if level=1)
     -3: possible (if level=3)
*)
let check_learn_pointsto {ctx=ctx; solv=solv; z3_names=z3_names} form1 form2 i2 level =
  match (List.nth form2.sigma i2) with
  | Slseg _ | Dlseg _ -> -1 (* Slseg/Dlseg is skipped, only Hpointsto is allowed in this function *)
  | Hpointsto (a,_,_) ->
    let rhs = (expr_to_solver_only_exp ctx z3_names a) in (* It is safe to leave undef without ex. quantification *)
    (* create list of equalities between form2.sigma[i2] and all items in form1.sigma *)
    let rec list_eq pointsto_list =
      match pointsto_list with
      | [] -> []
      | first::rest ->
        (match first with
        | Hpointsto (a,_, _) -> 
      		let lhs=(expr_to_solver_only_exp ctx z3_names a) in
		[Boolean.mk_eq ctx rhs lhs]
        | Slseg (a,_,_) -> 
      		let lhs=(expr_to_solver_only_exp ctx z3_names a) in
		[Boolean.mk_eq ctx
              	(Expr.mk_app ctx z3_names.base [rhs])
              	(Expr.mk_app ctx z3_names.base [lhs])]
        | Dlseg (a,_,b,_,_) -> 
      		let lhs1=(expr_to_solver_only_exp ctx z3_names a) in
      		let lhs2=(expr_to_solver_only_exp ctx z3_names b) in
		[Boolean.mk_eq ctx
              	(Expr.mk_app ctx z3_names.base [rhs])
              	(Expr.mk_app ctx z3_names.base [lhs1]);
		Boolean.mk_eq ctx
              	(Expr.mk_app ctx z3_names.base [rhs])
              	(Expr.mk_app ctx z3_names.base [lhs2])]
        ) @ list_eq rest
    in
    (* in the level 3, form2 is added within th try_learn_poinsto function into the solver. Therefore we do not need to add it here *)
    let query = match (list_eq form1.sigma),level with
      | [],1 -> [ (Boolean.mk_and ctx (formula_to_solver ctx form2)) ]
      | a,1 -> [ (Boolean.mk_not ctx (Boolean.mk_or ctx a));
          	(Boolean.mk_and ctx (formula_to_solver ctx form2)) ]
      | [],_ -> [ ]
      | a,_ -> [ (Boolean.mk_not ctx (Boolean.mk_or ctx a)) ]
    in
    match level with
    | 1 ->   if ((Solver.check solv query)=SATISFIABLE) then
        find_z ctx solv z3_names form1 0 form2 i2
      else -1
    | 3 -> if ((Solver.check solv query)=SATISFIABLE) then -3 else -1
    | _ -> -1


(* try to apply learn1 rule for pointsto *)
let try_learn_pointsto solver form1 form2 level _ =
  let ctx=solver.ctx in
  let z3_names=solver.z3_names in
  let common_part=match level with
  | 1 -> [Boolean.mk_and ctx (formula_to_solver ctx form1)] 
  | _ ->  [Boolean.mk_and ctx (formula_to_solver ctx form1); 
  	(Boolean.mk_and ctx (formula_to_solver ctx form2))]
  in
  Solver.push solver.solv;
  Solver.add solver.solv common_part;
  (* first find index of the rule on RHS, which can be learned on LHS *)
  let rec get_index i =
    if (List.length form2.sigma) <= i
    then (-1,-1)
    else
      let res=check_learn_pointsto solver form1 form2 i level in
      if res=(-1)
      then  get_index (i+1)
      else (res,i) (* res - index of z, i - index of x*)
  in
  let nequiv a b = not (a=b) in
  let remove k form =
    { pi=form.pi;
      sigma=List.filter (nequiv (List.nth form.sigma k)) form.sigma }
  in
  (* learn part is dropped 
     -- if the size is 0 and 
     -- the pointsto is not at the base adress *)
  let get_learned_part index=
      let (y2,size2,dest2) = to_hpointsto_unsafe (List.nth form2.sigma index) in
      (* try to find exact size *)
      let size_simplified=
        match try_simplify_SL_expr_to_int solver {sigma=[]; pi=form1.pi@form2.pi} size2 with
		| None -> size2
		| Some a -> Exp.Const (Int a)
		
      in
      let y2_z3=expr_to_solver_only_exp ctx z3_names y2 in
      let query=[Boolean.mk_eq ctx y2_z3 (Expr.mk_app ctx z3_names.base [y2_z3])] in
      if (size_simplified=Exp.zero)&&(Solver.check solver.solv query)=UNSATISFIABLE
	then {sigma=[]; pi=[]}
	else {sigma=[Hpointsto (y2,size_simplified,dest2)]; pi=[]}
  in

  match (get_index 0) with
  | (-1,-1) -> Solver.pop solver.solv 1; Fail
  | (-3,i2) ->  
    (* learn with level 3 *)
      let learned_part=get_learned_part i2 in
      Solver.pop solver.solv 1;
      Apply ( { sigma=form1.sigma; pi = form1.pi},
         (remove i2 form2),
         learned_part,
         [],
         NoRecord)
  | (i1,i2) -> 
      (* learn with level 1 *)
      let (y1,_,_) = to_hpointsto_unsafe (List.nth form1.sigma i1) in
      let (y2,_,_) = to_hpointsto_unsafe (List.nth form2.sigma i2) in
      let learned_part=get_learned_part i2 in
      Solver.pop solver.solv 1;
      Apply ( { sigma=form1.sigma; pi = (BinOp ( Pneq, y1,y2))::form1.pi},
        (remove i2 form2),
        learned_part,
        [],
        NoRecord)

(**** LEARN - Slseg ****)
(* check whether we can apply learn on the form2.sigma[i2].
   The result is false: imposible
     true: possible
*)

let check_learn_slseg {ctx=ctx; solv=solv; z3_names=z3_names} form1 form2 i2 level =
  let ff = Boolean.mk_false ctx in
  let rhs,rhs2=match (List.nth form2.sigma i2) with
	  | Hpointsto (_,_,_) ->  ff,ff
	  | Slseg (a,_,_) -> (expr_to_solver_only_exp ctx z3_names a),(expr_to_solver_only_exp ctx z3_names a)
	  | Dlseg (a,_,b,_,_) -> (expr_to_solver_only_exp ctx z3_names a),(expr_to_solver_only_exp ctx z3_names b)
  in
  if (rhs==ff) then false
  else
    (* create diffbase(rhs) and diffls(rhs) *)
    let rec list_eq sigma =
      match sigma with
      | [] -> []
      | first::rest ->
        (match first with
        | Hpointsto (a,_, _) -> 
        	let lhs=expr_to_solver_only_exp ctx z3_names a in
		let eq1=Boolean.mk_eq ctx
        	      (Expr.mk_app ctx z3_names.base [rhs])
	              (Expr.mk_app ctx z3_names.base [lhs]) 
		in
		let eq2=Boolean.mk_eq ctx
        	      (Expr.mk_app ctx z3_names.base [rhs2])
	              (Expr.mk_app ctx z3_names.base [lhs]) 
		in
		if (rhs2==ff) then [eq1] else [eq1;eq2]
        | Slseg (a,_,_) -> 
        	let lhs=expr_to_solver_only_exp ctx z3_names a in
		let eq1=Boolean.mk_eq ctx rhs (lhs) in
		let eq2=Boolean.mk_eq ctx rhs2 (lhs) in
		if (rhs2==ff) then [eq1] else [eq1;eq2]
	| Dlseg (a,_,b,_,_) ->
        	let lhs1=expr_to_solver_only_exp ctx z3_names a in
        	let lhs2=expr_to_solver_only_exp ctx z3_names b in
		let eq1=[Boolean.mk_eq ctx rhs (lhs1); Boolean.mk_eq ctx rhs (lhs2)] in
		let eq2=[Boolean.mk_eq ctx rhs2 (lhs1); Boolean.mk_eq ctx rhs2 (lhs2)] in
		if (rhs2==ff) then eq1 else (eq1@eq2)
        ) @ list_eq rest
    in
    match level with
    | 1 -> (match  (list_eq form1.sigma) with
      | [] -> false (* learn1 can not be applied with empty sigma on LHS *)
      | a ->
        let query = [ (Boolean.mk_or ctx a)]
        in
        (Solver.check solv query)=UNSATISFIABLE
      )
    | 2 ->   let query =
        match (list_eq form1.sigma) with
        | [] -> []
        | a ->   [ (Boolean.mk_not ctx (Boolean.mk_or ctx a))]
      in
      (Solver.check solv query)=SATISFIABLE
    | _ -> raise (TempExceptionBeforeApiCleanup "check_learn_slseg")

(* try to apply learn rule for slseg *)
let try_learn_slseg solver form1 form2 level _=
  let ctx=solver.ctx in
  let common_part=match level with
  | 1 -> [Boolean.mk_and ctx (formula_to_solver ctx form1)]
  | 2 -> [(Boolean.mk_and ctx (formula_to_solver ctx form1));
          (Boolean.mk_and ctx (formula_to_solver ctx form2))] 
  | _ -> []
  in
  Solver.push solver.solv;
  Solver.add solver.solv common_part;
  (* first find index of the rule on RHS, which can be learned on LHS *)
  let rec get_index i =
    if (List.length form2.sigma) <= i
    then -1
    else
      if (check_learn_slseg solver form1 form2 i level)
      then i
      else get_index (i+1)
  in
  let nequiv a b = not (a=b) in
  let remove k form =
    { pi=form.pi;
      sigma=List.filter (nequiv (List.nth form.sigma k)) form.sigma }
  in
  match (get_index 0) with
  | -1 -> Solver.pop solver.solv 1; Fail
  | i -> Solver.pop solver.solv 1; Apply ( { sigma=form1.sigma; pi = form1.pi},
      (remove i form2),
      {sigma=[List.nth form2.sigma i]; pi=[]},
      [],
      NoRecord)

(************************************************************)
(******* SPLIT rules ******)

let check_split_left {ctx=ctx; solv=solv; z3_names=z3_names} form1 i1 form2 i2 level =
  let ff = Boolean.mk_false ctx in
  let ff_noZ3 = Exp.Const (Bool false) in
  let lhs,lhs_size,lhs_noZ3,lhs_size_noZ3 =
    match (List.nth form1.sigma i1) with
    | Hpointsto (a,s ,_) -> (expr_to_solver_only_exp ctx z3_names a),(expr_to_solver_only_exp ctx z3_names s),a,s
    | Slseg _ | Dlseg _ -> ff,ff,ff_noZ3,ff_noZ3
  in
  let rhs,rhs_size,rhs_noZ3,rhs_size_noZ3 =
    match (List.nth form2.sigma i2) with
    | Hpointsto (a,s ,_) -> (expr_to_solver_only_exp ctx z3_names a),(expr_to_solver_only_exp ctx z3_names s),a,s
    | Slseg _ | Dlseg _ -> ff,ff,ff_noZ3,ff_noZ3
  in
  if ((lhs=ff)||(rhs=ff))
  then false
  else
  match level with
  | 0 -> (* static query for split without calling a solver *)
  	(match lhs_noZ3,rhs_noZ3,lhs_size_noZ3, rhs_size_noZ3 with
	| Exp.Var l, Exp.Var r, Exp.Const (Int l_size), Exp.Const (Int r_size) ->
		let l_cl = l::(get_equiv_vars [l] form1.pi) in
		let r_cl = r::(get_equiv_vars [r] form2.pi) in
		let mem lst x =
		    let eq y= (x=y) in
		    List.exists eq lst
  		in
		let rec intersect l1 l2 =
			match l1 with
			| [] -> false
			| first::rest -> if (mem l2 first) then true else (intersect rest l2)
		in
		((intersect l_cl r_cl)&&(l_size>r_size))
	| _,_,Exp.Const (Int l_size), Exp.Const (Int r_size) -> ((lhs_noZ3 = rhs_noZ3)&&(l_size>r_size))
	| _ -> false
	)

  | 1 ->
    let query=[
      Boolean.mk_not ctx (
        Boolean.mk_and ctx [
        (BitVector.mk_sle ctx lhs rhs);
        (BitVector.mk_sge ctx (BitVector.mk_add ctx lhs lhs_size) (BitVector.mk_add ctx rhs rhs_size) );
        (BitVector.mk_sgt ctx lhs_size rhs_size)
        ] )
    ] in
    (Solver.check solv query)=UNSATISFIABLE
    (*&& ((Solver.check solv query_null)=UNSATISFIABLE || (lhs_dest = Undef))*) (* here we may thing about better Undef recognition *)
  | 2 ->
    let query=[
      Boolean.mk_not ctx (
        Boolean.mk_and ctx [
        (BitVector.mk_sle ctx lhs rhs);
        (BitVector.mk_sge ctx (BitVector.mk_add ctx lhs lhs_size) (BitVector.mk_add ctx rhs rhs_size) );
        (BitVector.mk_sge ctx lhs_size rhs_size)
        ] )
    ] in
    let query2=[(BitVector.mk_sgt ctx lhs_size rhs_size)] in (* check that lhs_size can be really > rhs size *)
    (Solver.check solv query)=UNSATISFIABLE && (Solver.check solv query2)=SATISFIABLE
    (* &&((Solver.check solv query_null)=UNSATISFIABLE || (lhs_dest = Undef)) *)(* here we may thing about better Undef recognition *)
  | 4 ->
    let query=[
      (BitVector.mk_sle ctx lhs rhs);
      (Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [lhs]) (Expr.mk_app ctx z3_names.base [rhs]));
      (BitVector.mk_sge ctx (BitVector.mk_add ctx lhs lhs_size) (BitVector.mk_add ctx rhs rhs_size) );
      (BitVector.mk_sgt ctx lhs_size rhs_size) 
    ] in
    (Solver.check solv query)=SATISFIABLE 
      (*&& ((Solver.check solv query_null)=UNSATISFIABLE || (lhs_dest = Undef))*) (* here we may thing about better Undef recognition *)
  | _ -> raise (TempExceptionBeforeApiCleanup "check_split_left")

let check_split_right {ctx=ctx; solv=solv; z3_names=z3_names} form1 i1 form2 i2 level =
  let ff = Boolean.mk_false ctx in
  let ff_noZ3 = Exp.Const (Bool false) in
  let lhs,lhs_size,lhs_noZ3,lhs_size_noZ3 =
    match (List.nth form1.sigma i1) with
    | Hpointsto (a,s ,_) -> (expr_to_solver_only_exp ctx z3_names a),(expr_to_solver_only_exp ctx z3_names s),a,s
    | Slseg _ | Dlseg _ -> ff,ff,ff_noZ3,ff_noZ3
  in
  let rhs,rhs_size,rhs_noZ3,rhs_size_noZ3 =
    match (List.nth form2.sigma i2) with
    | Hpointsto (a,s ,_) -> (expr_to_solver_only_exp ctx z3_names a),(expr_to_solver_only_exp ctx z3_names s),a,s
    | Slseg _ | Dlseg _ -> ff,ff,ff_noZ3,ff_noZ3
  in
  if ((lhs=ff)||(rhs=ff))
  then false
  else
  match level with
  | 0 -> (* static query for split without calling a solver *)
  	(match lhs_noZ3,rhs_noZ3,lhs_size_noZ3, rhs_size_noZ3 with
	| Exp.Var l, Exp.Var r, Exp.Const (Int l_size), Exp.Const (Int r_size) -> 
		let l_cl = l::(get_equiv_vars [l] form1.pi) in
		let r_cl = r::(get_equiv_vars [r] form2.pi) in
		let mem lst x =
		    let eq y= (x=y) in
		    List.exists eq lst
  		in
		let rec intersect l1 l2 =
			match l1 with
			| [] -> false
			| first::rest -> if (mem l2 first) then true else (intersect rest l2)
		in

		((intersect l_cl r_cl)&&(l_size<r_size))
	| _,_,Exp.Const (Int l_size), Exp.Const (Int r_size) -> ((lhs_noZ3 = rhs_noZ3)&&(l_size<r_size))
	| _ -> false
	)
  | 1 ->
    let query=[
      Boolean.mk_not ctx (
        Boolean.mk_and ctx [
        (BitVector.mk_sge ctx lhs rhs);
        (BitVector.mk_sle ctx (BitVector.mk_add ctx lhs lhs_size) (BitVector.mk_add ctx rhs rhs_size) );
        (BitVector.mk_slt ctx lhs_size rhs_size)
        ] )
    ] in
    (Solver.check solv query)=UNSATISFIABLE 
    (* && ((Solver.check solv query_null)=UNSATISFIABLE || (rhs_dest = Undef))*) (* here we may thing about better Undef recognition *)
  | 2 ->
    let query=[
      Boolean.mk_not ctx (
        Boolean.mk_and ctx [
        (BitVector.mk_sge ctx lhs rhs);
        (BitVector.mk_sle ctx (BitVector.mk_add ctx lhs lhs_size) (BitVector.mk_add ctx rhs rhs_size) );
        (BitVector.mk_sle ctx lhs_size rhs_size)
        ] )
     ] in
    let query2=[(BitVector.mk_slt ctx lhs_size rhs_size)] in (* check that lhs_size can be really < rhs size *)
    (Solver.check solv query)=UNSATISFIABLE && (Solver.check solv query2)=SATISFIABLE
    (* && ((Solver.check solv query_null)=UNSATISFIABLE || (rhs_dest = Undef))*) (* here we may thing about better Undef recognition *)
  | 4 ->
    let query=[
      (BitVector.mk_sge ctx lhs rhs);
      (Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [lhs]) (Expr.mk_app ctx z3_names.base [rhs]));
      (BitVector.mk_sle ctx (BitVector.mk_add ctx lhs lhs_size) (BitVector.mk_add ctx rhs rhs_size) );
      (BitVector.mk_slt ctx lhs_size rhs_size)
    ] in
    (Solver.check solv query)=SATISFIABLE 
    (* && ((Solver.check solv query_null)=UNSATISFIABLE || (rhs_dest = Undef)) *) (* here we may thing about better Undef recognition *)
  | _ -> raise (TempExceptionBeforeApiCleanup "check_split_right")


let rec find_split_ll solver form1 i1 form2 level=
  let (*rec*) try_with_rhs i2 =
    if (List.length form2.sigma) <= i2
    then -1,-1
    else (if (check_split_left solver form1 i1 form2 i2 level)
      then i2,1
      else ( if (check_split_right solver form1 i1 form2 i2 level)
        then i2,2
        else -1,-1))
  in
  if (List.length form1.sigma) <= i1
  then (-1,-1,-1)
  else
    match (try_with_rhs 0) with
    | -1,_ -> (find_split_ll solver form1 (i1+1) form2 level)
    | x,lr -> (i1,x,lr)

let find_split solver form1 form2 level =
  let ctx=solver.ctx in
  let common_part=match level with
  | 1 -> [Boolean.mk_and ctx (formula_to_solver ctx form1)]
  | 2 | 4 -> [(Boolean.mk_and ctx (formula_to_solver ctx form1));
          (Boolean.mk_and ctx (formula_to_solver ctx form2))]
  | _ -> []
  in
  Solver.push solver.solv;
  Solver.add solver.solv common_part;
  let res= find_split_ll solver form1 0 form2 level in
  Solver.pop solver.solv 1; res



let try_split {ctx=ctx; solv=solv; z3_names=z3_names} form1 form2 level pvars =
  let variables=(find_vars form1)@(find_vars form2)@pvars in
  let mem lst x =
    let eq y= (x=y) in
    List.exists eq lst
  in
  let rec get_fresh_var seed confl=
    if (mem confl seed)
    then get_fresh_var (seed+1) confl
    else seed
  in
  let m=find_split {ctx;solv;z3_names} form1 form2 level in
  let nequiv a b = not (a=b) in
  let remove k form =
    { pi=form.pi;
      sigma=List.filter (nequiv (List.nth form.sigma k)) form.sigma }
  in
  match m with
  | (-1,-1,-1) -> Fail
  | (i1,i2,leftright) ->
    let x1,s1,y1 = to_hpointsto_unsafe (List.nth form1.sigma i1) in
    let x2,s2,y2 = to_hpointsto_unsafe (List.nth form2.sigma i2) in
    match leftright with
    | 1 -> (* split left *)
      print_string "Splitleft ";
      (* Compute size of the first block -- Check form1 /\ form2 -> size_first=0 *)
      let size_first=
        let tmp_size_first=(Exp.BinOp (Pminus,x2,x1)) in
	(* try to get exact size *)
        match try_simplify_SL_expr_to_int {ctx=ctx; solv=solv; z3_names=z3_names} {sigma=[]; pi=form1.pi@form2.pi} tmp_size_first with
		| None -> tmp_size_first
		| Some a -> Exp.Const (Int a)
      in
      (* Compute size of the last block -- Check form1 /\ form2 -> size_last=0 *)
      let size_last=
        let tmp_size_last=
          if size_first=(Exp.zero)
          then (Exp.BinOp(Pminus,s1,s2))
          else (Exp.BinOp(Pminus,s1,Exp.BinOp(Pplus,s2,size_first))) in
	(* try to find exact size *)
        match try_simplify_SL_expr_to_int {ctx=ctx; solv=solv; z3_names=z3_names} {sigma=[]; pi=form1.pi@form2.pi} tmp_size_last with
		| None -> tmp_size_last
		| Some a -> Exp.Const (Int a)
      in
      (* pointer to the last segment *)
      let ptr_last=(Exp.BinOp(Pplus,x2,s2)) in
      let ptr_last_var = get_fresh_var 1 variables in
      let ptr_last_eq = (Exp.BinOp (Peq,Exp.Var ptr_last_var,ptr_last)) in
      (* destination of the split (null/undefined)*)
      (* TODO: string: undef + end of string or char +...+ end of string *)
      let split_dest=
        let query_null=[ expr_to_solver_only_exp ctx z3_names (BinOp (Pneq,y1, Exp.zero));
          (Boolean.mk_and ctx (formula_to_solver ctx form1))
        ] in
        if (Solver.check solv query_null)=UNSATISFIABLE then Exp.zero else Exp.Undef
      in
      let sigma1_new,pi_tmp1, pi_tmp2, new_lvars= (* compute the splitted part of sigma and new pi*)
        if size_first=(Exp.zero) then
          [ Hpointsto (x1,s2,split_dest);
            Hpointsto (Exp.Var ptr_last_var,size_last,split_dest)],
          [ Exp.BinOp(Peq,x1,x2);
            BinOp ( Plesseq, s1, UnOp ( Len, x1));
            BinOp ( Peq, UnOp ( Base, x1), UnOp ( Base, Var ptr_last_var));
            ptr_last_eq],
          [ Exp.BinOp(Plesseq,s2,s1) ],
          [ ptr_last_var ]
        else if size_last=(Exp.zero) then
          [ Hpointsto (x1,size_first,split_dest);
            Hpointsto (x2,s2,split_dest)],
          [ BinOp(Peq,BinOp(Pplus,x2,s2),BinOp(Pplus,x1,s1));
            BinOp ( Plesseq, s1, UnOp ( Len, x1));
            BinOp ( Peq, UnOp ( Base, x1), UnOp ( Base, x2))],
          [ BinOp(Plesseq,s2,s1) ],
          []
        else
          [ Hpointsto (x1,size_first,split_dest);
            Hpointsto (x2,s2,split_dest);
            Hpointsto (Var ptr_last_var,size_last,split_dest)],
          [ BinOp ( Plesseq, s1, UnOp ( Len, x1));
            BinOp ( Peq, UnOp ( Base, x1), UnOp ( Base, x2));
            BinOp ( Peq, UnOp ( Base, x1), UnOp ( Base, ptr_last));
            ptr_last_eq],
          [ (* BinOp(Plesseq,x1,x2); *)
            BinOp(Plesseq,s2,s1)(* ;
            BinOp(Plesseq,BinOp(Pplus,x2,s2),BinOp(Pplus,x1,s1)) *) ],
          [ ptr_last_var ]
      in
      let new_pi=
        if (level=1) then pi_tmp1 (* form1 -> pi_tmp2, no need to add this information *)
        else pi_tmp1 @ pi_tmp2
      in
      Apply (  {sigma=sigma1_new@ (remove i1 form1).sigma; pi=form1.pi @ new_pi},
        form2,
        {sigma=[]; pi=new_pi},
        new_lvars,
	NoRecord)

    | 2 ->   (* split right *)
      print_string "Split_right ";
      (* Compute size of the first block -- Check form1 /\ form2 -> size_first=0 *)
      let size_first=
        let tmp_size_first=(Exp.BinOp (Pminus,x1,x2)) in
	(* try to find exact size *)
        match try_simplify_SL_expr_to_int {ctx=ctx; solv=solv; z3_names=z3_names} {sigma=[]; pi=form1.pi@form2.pi} tmp_size_first with
		| None -> tmp_size_first
		| Some a -> Exp.Const (Int a)
		
      in
      (* Compute size of the last block -- Check form1 /\ form2 -> size_last=0 *)
      let size_last=
        let tmp_size_last=
          if size_first=(Exp.zero)
          then (Exp.BinOp(Pminus,s2,s1))
          else (Exp.BinOp(Pminus,s2,Exp.BinOp(Pplus,s1,size_first))) in
	  (* try to find exact size *)
          match try_simplify_SL_expr_to_int {ctx=ctx; solv=solv; z3_names=z3_names} {sigma=[]; pi=form1.pi@form2.pi} tmp_size_last with
		| None -> tmp_size_last
		| Some a -> Exp.Const (Int a)
		
      in
      (* pointer to the last block *)
      let ptr_last=(Exp.BinOp(Pplus,x1,s1)) in
      let ptr_last_var = get_fresh_var 1 variables in
      let ptr_last_eq = (Exp.BinOp (Peq,Exp.Var ptr_last_var,ptr_last)) in
      (* The RHS of the splitted points to can be 
         -- null 
         -- undef: we add a fresh variable for each piece
       we need to get a name of each particular part in the "recorded splits" *)
      let split_dest1,split_dest2,split_dest3,dest_vars=
        let query_null=[ expr_to_solver_only_exp ctx z3_names (BinOp (Pneq,y2, Exp.zero));
          (Boolean.mk_and ctx (formula_to_solver ctx form2))
        ] in
        if (Solver.check solv query_null)=UNSATISFIABLE
        then Exp.zero,Exp.zero,Exp.zero,[]
        else (
		let v1=get_fresh_var (ptr_last_var+1) ([ ptr_last_var]@variables) in
		let v2=get_fresh_var (v1+1) ([ptr_last_var;v1]@variables) in
		let v3=get_fresh_var (v2+1) ([ptr_last_var;v1;v2]@variables) in
		Exp.Var v1,Exp.Var v2, Exp.Var v3,[v1;v2;v3]
	)
      in
      let sigma2_new,pi_tmp1,pi_tmp2,new_lvars,deltas= (* compute the splitted part of sigma *)
        if size_first=(Exp.zero) then
          [ Hpointsto (x1,s1,split_dest2);
            Hpointsto (Var ptr_last_var,size_last,split_dest3)],
          [ Exp.BinOp(Peq,x1,x2); BinOp ( Plesseq, s2, UnOp ( Len, x2));
            ptr_last_eq; 
            BinOp(Peq,UnOp(Base,x1),UnOp(Base,Var ptr_last_var))],
          [ Exp.BinOp(Plesseq,s1,s2) ],
          [ ptr_last_var]@dest_vars,
          [ Exp.zero; s1 ]
        else if size_last=(Exp.zero) then
          [ Hpointsto (x2,size_first,split_dest1);
            Hpointsto (x1,s1,split_dest2)],
          [ BinOp(Peq,BinOp(Pplus,x2,s2),BinOp(Pplus,x1,s1));
            BinOp ( Plesseq, s2, UnOp ( Len, x2));
            BinOp ( Peq, UnOp ( Base, x1), UnOp ( Base, x2))],
          [ BinOp(Plesseq,s1,s2) ],
          dest_vars,
          [ Exp.zero; size_first ]
        else
	  let delta_last=match try_simplify_SL_expr_to_int 
	  		{ctx=ctx; solv=solv; z3_names=z3_names} {sigma=[]; pi=form1.pi@form2.pi} (BinOp(Pplus,size_first,s1)) with
		| None -> (Exp.BinOp(Pplus,size_first,s1))
		| Some a -> Exp.Const (Int a)
	  in	

          [ Hpointsto (x2,size_first,split_dest1);
            Hpointsto (x1,s1,split_dest2);
            Hpointsto (Var ptr_last_var,size_last,split_dest3)],
          [ BinOp ( Plesseq, s2, UnOp ( Len, x2));
            BinOp ( Peq, UnOp ( Base, x1), UnOp ( Base, x2));
            BinOp(Peq,UnOp(Base,x2),UnOp(Base,Var ptr_last_var));
            ptr_last_eq; ],
          [ (* BinOp(Plesseq,x2,x1); *)
            BinOp(Plesseq,s1,s2)(* ;
            BinOp(Plesseq,BinOp(Pplus,x1,s1),BinOp(Pplus,x2,s2)) *) ],
          [ ptr_last_var ]@dest_vars,
          [ Exp.zero; size_first; delta_last ]
      in
      let new_pi=
        if (level=1) then pi_tmp1 (* form1 -> pi_tmp2, no need to add this information *)
        else pi_tmp1 @ pi_tmp2
      in

      Apply ({sigma=form1.sigma; pi=form1.pi @ new_pi},
        {sigma=sigma2_new@ (remove i2 form2).sigma; pi=form2.pi},
        {sigma=[]; pi=new_pi},
        new_lvars,
	Record (List.nth form2.sigma i2, {sigma=sigma2_new; pi=new_pi}, deltas  ))
    | _ -> raise (TempExceptionBeforeApiCleanup "try_split")

(******************************************************************************)
(* Auxiliary functions and types for entailment 
   The functions entailment, entailment_ll, check_lambda_entailment, try_match and apply_match are in mutual recursion due to matching of SLSeg
   - the entailment is called to be sure that lambdas are compatible *)

type entailment_slseg_remove =
| RemOk of Formula.pi
| RemFail

let check_entailment_finish {ctx=ctx; solv=solv; z3_names=_} form1 form2 evars =
  if (List.length form1.sigma)>0 then -1
  else
  (
  (*print_endline (lvariables_to_string evars);*)
  (* First all Slseg(a,b,_) are replaced by a=b 
     and Dlseg(a,b,c,d,_) are prelaced by a=d and b=c --- i.e. empty lists *)
  let rec remove_lseg_form2 f2 =
    match f2.sigma with
    | [] -> RemOk f2.pi
    | Hpointsto _ :: _ -> RemFail
    | Slseg (a,b,_) :: rest ->
      (match (remove_lseg_form2 {pi=f2.pi; sigma=rest}) with
      | RemFail -> RemFail
      | RemOk f2_new -> RemOk (Exp.BinOp ( Peq, a, b):: f2_new)
      )
    | Dlseg (a,b,c,d,_) :: rest ->
      (match (remove_lseg_form2 {pi=f2.pi; sigma=rest}) with
      | RemFail -> RemFail
      | RemOk f2_new -> RemOk ([Exp.BinOp ( Peq, a, d); Exp.BinOp ( Peq, b, c)] @ f2_new)
      )


  in
  match (remove_lseg_form2 form2) with
  | RemFail -> 0
  | RemOk x ->
    (* form1 and form2(= x) contains now only pure parts. We want to check implication:
       (\ex. evars form1) -> (\ex. evars form2)
      In the implementation, we are checking UNSAT of [ form1 /\ not (\ex. evars form2) ]
    *)
    let get_z3_cons a=Expr.mk_const ctx (Symbol.mk_string ctx (string_of_int a)) (BitVector.mk_sort ctx bw_width) in
    let evars_z3=List.map get_z3_cons evars in
    let f2=Boolean.mk_and ctx (formula_to_solver_with_quantified_undefs ctx {pi=x; sigma=[]}) in
    let f2_q=create_ex_quantifier ctx evars_z3 f2 in
    let query = (Boolean.mk_not ctx f2_q) :: (formula_to_solver ctx form1) in
    if (Solver.check solv query)=UNSATISFIABLE then 1
    else 0
    )


(******************************************************************************)
(**** MATCH rules ****)
(* The level parameter gives the level of match, the only difference is in check_match function *)

(* Check whether match (of the given level) can be applied on i1^th pointsto on LHS and i2^th points-to on RHS *)
(* dir - direction of Dlseg vs. (Hpointsto/Slseg) match: 1 from the beginning 2 from the end. 
   When applied to something else then Dlseg on one side, false is returned. *)

let check_match {ctx=ctx; solv=solv; z3_names=z3_names} form1 i1 form2 i2 level dir =
  let ff = Boolean.mk_false ctx in
  let ff_noZ3 = Exp.Const (Bool false)in
  let lhs_ll,lhs_noZ3,flag_l =
    match (List.nth form1.sigma i1),dir with
    | Hpointsto (a,_ ,_),_ -> (expr_to_solver_only_exp ctx z3_names a),a,0
    | Slseg (a,_,_),_ -> (expr_to_solver_only_exp ctx z3_names a),a,1
    | Dlseg (a,_,_,_,_),1 -> (expr_to_solver_only_exp ctx z3_names a),a,5
    | Dlseg (_,_,a,_,_),_ -> (expr_to_solver_only_exp ctx z3_names a),a,5
  in
  let lhs_size,lhs_size_noZ3 =
    match (List.nth form1.sigma i1) with
    | Hpointsto (_, s ,_) -> (expr_to_solver_only_exp ctx z3_names s),s
    | Slseg _ | Dlseg _ -> ff,ff_noZ3 (* we do not speak about sizes before the slseg is unfolded *)
  in
  let rhs_ll,rhs_noZ3,flag_r =
    match (List.nth form2.sigma i2),dir with
    | Hpointsto (a,_ ,_),_ -> (expr_to_solver_only_exp ctx z3_names a),a,0
    | Slseg (a,_,_),_ -> (expr_to_solver_only_exp ctx z3_names a),a,1
    | Dlseg (a,_,_,_,_),1 -> (expr_to_solver_only_exp ctx z3_names a),a,5
    | Dlseg (_,_,a,_,_),_ -> (expr_to_solver_only_exp ctx z3_names a),a,5
  in
  let rhs_size,rhs_size_noZ3 =
    match (List.nth form2.sigma i2) with
    | Hpointsto (_, s ,_) -> (expr_to_solver_only_exp ctx z3_names s),s
    | Slseg _ | Dlseg _ -> ff,ff_noZ3 (* we do not speak about sizes before the slseg is unfolded *)
  in
  (* if dir !=1 then Dlseg must be exactly on one side --- i.e. (flag_l+flag_r=5). *)
  if ((dir>1)&&((flag_l+flag_r)!=5)) then false
  else
  (* Note that if one site contains list segment and the other one points-to then we compare bases
     within the SMT queries *)
  let lhs=if ((flag_l+flag_r)=1 || (flag_l+flag_r)=5)
    then (Expr.mk_app ctx z3_names.base [lhs_ll])
    else lhs_ll
  in
  let rhs=if ((flag_l+flag_r)=1 || (flag_l+flag_r)=5)
    then (Expr.mk_app ctx z3_names.base [rhs_ll])
    else rhs_ll
  in
  match level with
  | 0 -> (* static checks - no solver calls *)
  	(match lhs_noZ3,rhs_noZ3 with
	| Exp.Var l,Exp.Var r ->
		let l_cl = l::(get_equiv_vars [l] form1.pi) in
		let r_cl = r::(get_equiv_vars [r] form2.pi) in
		let mem lst x =
		    let eq y= (x=y) in
		    List.exists eq lst
	  	in
		let rec intersect l1 l2 =
			match l1 with
			| [] -> false
			| first::rest -> if (mem l2 first) then true else (intersect rest l2)
		in

		(intersect l_cl r_cl)&&((lhs_size=ff)||(rhs_size=ff)||(lhs_size_noZ3=rhs_size_noZ3))
	| _ -> (lhs_noZ3=rhs_noZ3) && ((lhs_size=ff)||(rhs_size=ff)||(lhs_size_noZ3=rhs_size_noZ3))
	)
  | 1 ->
    let query_size =
      if ((lhs_size=ff)||(rhs_size=ff)) then true
      else
        let qq1 =[
          Boolean.mk_not ctx (Boolean.mk_eq ctx lhs_size rhs_size)]
        in
      ((Solver.check solv qq1)=UNSATISFIABLE)
    in
    let query1 = [Boolean.mk_not ctx (Boolean.mk_eq ctx lhs rhs)]
    in
    query_size && ((Solver.check solv query1)=UNSATISFIABLE)
  | 2 ->
    let query_size =
      if ((lhs_size=ff)||(rhs_size=ff)) then true
      else
        let qq =[Boolean.mk_not ctx (Boolean.mk_eq ctx lhs_size rhs_size)] in
      (Solver.check solv qq)=UNSATISFIABLE
    in
    let query = [Boolean.mk_not ctx (Boolean.mk_eq ctx lhs rhs)]
    in
    query_size && ((Solver.check solv query)=UNSATISFIABLE)
  | 3 ->
    let query_size =
      if ((lhs_size=ff)||(rhs_size=ff)) then true
      else
        let qq1 =[
          Boolean.mk_not ctx (Boolean.mk_eq ctx lhs_size rhs_size) ]
        in
      ((Solver.check solv qq1)=UNSATISFIABLE)
    in
    let query1=[(Boolean.mk_and ctx (formula_to_solver ctx form2));
        (Boolean.mk_eq ctx lhs rhs)
      ]
    in
    let query2=[Boolean.mk_not ctx (Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [lhs]) (Expr.mk_app ctx z3_names.base [rhs]))] in
    query_size
    && ((Solver.check solv query1)=SATISFIABLE) && ((Solver.check solv query2)=UNSATISFIABLE)
  | 4 ->
    let query_size =
      if ((lhs_size=ff)||(rhs_size=ff)) then true
      else
        let qq =[
          Boolean.mk_not ctx (Boolean.mk_eq ctx lhs_size rhs_size)] in
      (Solver.check solv qq)=UNSATISFIABLE
    in
    let query=[(Boolean.mk_eq ctx lhs rhs)] in
    query_size && ((Solver.check solv query)=SATISFIABLE)
  | _ -> false

(* Find pair of points-to for match. Return (-1,-1) if unposibble *)
let rec find_match_ll solver form1 i1 form2 level  =
  let rec try_with_rhs i2 =
    if (List.length form2.sigma) <= i2
    then -1,-1
    else (if (check_match solver form1 i1 form2 i2 level 1)
      then i2,1
      else (if (check_match solver form1 i1 form2 i2 level 2)
      	then i2,2 
	else (try_with_rhs (i2+1)))
    )
  in
  if (List.length form1.sigma) <= i1
  then (-1,-1,-1)
  else
    match (try_with_rhs 0) with
    | -1,_ -> (find_match_ll solver form1 (i1+1) form2 level)
    | x,dir -> (i1,x,dir)

let find_match solver form1 form2 level =
  let ctx=solver.ctx in
  let common_part=match level with
  | 1 | 3 -> [Boolean.mk_and ctx (formula_to_solver ctx form1)]
  | 2 | 4 -> [(Boolean.mk_and ctx (formula_to_solver ctx form1));
          (Boolean.mk_and ctx (formula_to_solver ctx form2))] 
  | _ -> []
  in
  Solver.push solver.solv;
  Solver.add solver.solv common_part;
  let res=find_match_ll solver form1 0 form2 level in
  Solver.pop solver.solv 1; res



(* apply the match rule to i=(i1,i2)
   pred_type=0 --- pointsto x pointsto
   pred_type=1 --- pointsto x Slseg
   pred_type=2 --- Slseg x pointsto
   pred_type=3 --- Slseg x Slseg
*)
type apply_match_res =
| ApplyOK of Formula.t * Formula.t * variable list
| ApplyFail

(* NOTE that apply_match, try_match, entailment_ll, entailment and check_lambda_entailment are in mutual recursion *)
(* To break the mutual recursion, you can replace entailment call in apply_match by equality of lambdas *)

let rec apply_match solver i pred_type form1 form2 pvars dir =
  let nequiv a b = not (a=b) in
  let remove k form =
    { pi=form.pi;
      sigma=List.filter (nequiv (List.nth form.sigma k)) form.sigma }
  in
  match i with
  | (i1,i2) ->
    match pred_type with
    | 0 -> ApplyOK ((remove i1 form1), (remove i2 form2), [])
    | 1 | 10 -> let new_form2,new_lvars=unfold_predicate form2 i2 ((find_vars form1)@pvars) dir in
      ApplyOK (form1, new_form2, new_lvars)
    | 2 | 20 -> let new_form1,new_lvars=unfold_predicate form1 i1 ((find_vars form2)@pvars) dir in
      ApplyOK (new_form1, form2, new_lvars)
    | 3 ->
      let _,y1,ls1 = to_slseg_unsafe  (List.nth form1.sigma i1) in
      let _,y2,ls2 = to_slseg_unsafe (List.nth form2.sigma i2) in
      (*if (ls1=ls2) then *) (* Use this line to break the mutual recursion. *)
      if (check_lambda_entailment (config_solver_to 2000) ls1 ls2)=1 then
        let lhs=(remove i1 form1) in
        let rhs_tmp=(remove i2 form2) in
        let rhs={sigma=(Slseg (y1,y2,ls2))::rhs_tmp.sigma; pi=rhs_tmp.pi} in
        ApplyOK (lhs, rhs, [])
	
      else  ApplyFail
    | 30 ->
      let a1,b1,c1,d1,ls1 = to_dlseg_unsafe  (List.nth form1.sigma i1) in
      let a2,b2,c2,d2,ls2 = to_dlseg_unsafe (List.nth form2.sigma i2) in
      (*if (ls1=ls2) then *) (* Use this line to break the mutual recursion. *)
      let lhs=(remove i1 form1) in
      let rhs_tmp=(remove i2 form2) in
      (match (check_lambda_entailment solver ls1 ls2),dir with
      | 1,1 ->
      		let rhs={sigma=(Dlseg (d1,c1,c2,d2,ls2))::rhs_tmp.sigma; pi=rhs_tmp.pi} in
        	ApplyOK (lhs, rhs, [])
      | 1,2 ->
      		let rhs={sigma=(Dlseg (a2,b2,b1,a1,ls2))::rhs_tmp.sigma; pi=rhs_tmp.pi} in
        	ApplyOK (lhs, rhs, [])
      | _ -> ApplyFail
      )
    (*| _ -> raise (TempExceptionBeforeApiCleanup "apply_match")*)
    | _ -> ApplyFail


(* Try to apply match rule. The result is:
1:  form1 - the LHS formula with removed matched part and added equality x=y
  form2 - the RHS formula with removed matched part
  M - the learned part
2:  unfolded Slseg in form1/form2 and added equality x=y

*)
and try_match solver form1 form2 level pvars  =
  let m=find_match solver form1 form2 level in
  match m with
  | (-1,-1,_) -> Fail
  | (i1,i2,dir) ->
    let x1,y1,backx1,backy1,type1,size1=match (List.nth form1.sigma i1) with
      | Hpointsto (a,size,b) -> (a,b,Exp.Void,Exp.Void,0,size)
      | Slseg (a,b,_) -> (a,b,Exp.Void,Exp.Void,2,Exp.Void) 
      | Dlseg (a,b,c,d,_) -> (a,d,c,b,20,Exp.Void) in
    let x2,y2,backx2,backy2,type2,size2=match (List.nth form2.sigma i2) with
      | Hpointsto (a,size,b) -> (a,b,Exp.Void,Exp.Void,0,size)
      | Slseg (a,b,_) -> (a,b,Exp.Void,Exp.Void,1,Exp.Void) 
      | Dlseg (a,b,c,d,_) -> (a,d,c,b,10,Exp.Void) in
    match apply_match solver (i1,i2) (type1+type2) form1 form2 pvars dir with
    | ApplyFail -> Fail
    | ApplyOK (f1,f2,added_lvars) ->
      (* x1 = x2 if equal predicate types match. Othervice base(x1) = base(x2) is added. *)
      let x_eq,dll_eq=match (type1+type2),dir with
      | 0,1 | 3,1 -> [Exp.BinOp ( Peq, x1,x2)],[]
      | 30,1 -> [Exp.BinOp ( Peq, x1,x2)],[Exp.BinOp ( Peq, backy1,backy2)]
      | _,1 -> [Exp.BinOp ( Peq, Exp.UnOp(Base,x1), Exp.UnOp(Base,x2))],[]
      | 10,2 -> [Exp.BinOp ( Peq, Exp.UnOp(Base,x1), Exp.UnOp(Base,backx2))],[]
      | 20,2 -> [Exp.BinOp ( Peq, Exp.UnOp(Base,backx1), Exp.UnOp(Base,x2))],[]
      (*| 30,2 -> [Exp.BinOp ( Peq, backx1,backx2)],[Exp.BinOp ( Peq, y1,y2)]*) (* not needed, two Dlsegs are match in the equal direction *)
      | _ -> raise (TempExceptionBeforeApiCleanup "try_match: 1")
      in
      (* y1 = y2 is added only if Hpointsto is mathced with Hpointsto *)
      let y_eq=if (type1+type2)=0 then [(Exp.BinOp ( Peq, y1,y2))] else [] in
      (* size1 = size2 is added if Hpointsto is mathced with Hpointsto *)
      let size_eq=if (type1+type2)=0 then [(Exp.BinOp ( Peq, size1,size2))] else [] in
      match level with
      | 1 ->   Apply ( { sigma=f1.sigma; pi = y_eq @ dll_eq @ f1.pi},
          f2,
          {sigma=[]; pi=dll_eq},
          added_lvars,NoRecord)
      | 0 | 3 ->   Apply ( { sigma=f1.sigma; pi = x_eq @ y_eq @ dll_eq @ f1.pi},
          f2,
          {sigma=[]; pi=x_eq @ dll_eq},
          added_lvars,NoRecord)
      | _ ->   Apply ( { sigma=f1.sigma; pi = x_eq @ y_eq @ dll_eq @ size_eq @ f1.pi},
          f2,
          {sigma=[]; pi=x_eq @ dll_eq @ size_eq},
          added_lvars,NoRecord)




(****************************************************)
(* use entailment to check entailment between lambdas 
  results: 0: no entailment, 1: lambda1 |= lambda2, 2: lambda2 |= lambda1 
*)


and check_lambda_entailment solver lambda1 lambda2 =
	if not ((List.length lambda1.param) = (List.length lambda2.param)) then 0
	else
	let variables= (find_vars lambda1.form) @ (find_vars lambda2.form) in
	let rec fresh_var_id intlist id=
		match intlist with 
		| [] -> id
		| first::rest -> if (first>=id) then fresh_var_id rest (first+1) else fresh_var_id rest id 
	in
	let rec get_unique_lambda_params params id =
		match params with
		| [] -> []
		| _::rest -> id::(get_unique_lambda_params rest (id+1))
	in
	let new_params=get_unique_lambda_params lambda1.param (fresh_var_id variables 0) in
	let rec rename_params form oldparams newparams =
		match oldparams,newparams with
		| [],[] -> form
		| p1::rest1,p2::rest2 -> rename_params (substitute_vars p2 p1 form) rest1 rest2
		| _ -> raise (TempExceptionBeforeApiCleanup "check_lambda_entailment") (*{sigma=[];pi=[]}*)
	in
	let lambda1_new= rename_params lambda1.form lambda1.param new_params in
	let lambda2_new= rename_params lambda2.form lambda2.param new_params in
	print_endline "LAMBDA entailment:";
	Formula.print lambda1_new;
	Formula.print lambda2_new;
	match (entailment solver lambda1_new lambda2_new variables), 
		(entailment solver lambda2_new lambda1_new variables)
	with
	| true,_ -> 1
	| false,true -> 2
	| _ -> 0


(****************************************************)
(* ENTAILMENT using match1 rules *)

and entailment_ll solver form1 form2 evars=
(* check entailment between form1 and form2 using match1 rules *)
  match (check_entailment_finish solver form1 form2 evars) with
  | 0 -> false
  | 1 -> true
  | -1 ->
     (match (try_match solver form1 form2 0 []),(try_match solver form1 form2 2 []) with
     | Apply (f1,f2,_,_,_),_ ->
  		print_string "Match, "; flush stdout;
  		(entailment_ll solver f1 f2 evars)
     | Fail,Apply (f1,f2,_,_,_) ->
  		print_string "Match2, "; flush stdout;
  		(entailment_ll solver f1 f2 evars)
     | Fail,Fail -> false)
  | _ -> raise (TempExceptionBeforeApiCleanup "entailment_ll")

and entailment solver form1 form2 evars=
  (* get fresh names for the evars to avoid conflicts in the entailment query *)
  let form1_s=Formula.simplify form1 evars in
  let form2_s=Formula.simplify form2 evars in
  (*
  print_string "XXXXXXXXXXXXXXXXXXXXXX\nFORM1: ";
  Formula.print_with_lambda form1_s;
  print_string "FORM2: ";
  Formula.print_with_lambda form2_s;
  print_endline (lvariables_to_string evars); *)
  let conflicts1=find_vars form1_s in
  let form2_rename,evars2=match (rename_ex_variables form2_s evars conflicts1) with
    | f -> f
  in
  let conflicts2=find_vars form2_rename in
  let form1_rename,evars1=match (rename_ex_variables form1_s evars2 conflicts2) with
    | f -> f
  in
  let query=(formula_to_solver solver.ctx form1_rename) @ (formula_to_solver solver.ctx form2_rename) in
  let res=
  	(Solver.check solver.solv query)=SATISFIABLE && (entailment_ll solver form1_rename form2_rename (evars@evars1@evars2))
  in
  if res then print_endline "ENT VALID" else print_endline "ENT INVALID"; flush stdout;
  res

(****************************************************)
(* MAIN biabduction procedure *)

(* Test SAT of (form1 /\ form2) and check finish *)
type sat_test_res =
| Finish of Formula.t * Formula.t
| NoFinish
| SatFail


let rec prune_pure_form1 pi=
  	match pi with
	| [] -> []
	| Formula.Exp.UnOp (Freed,_)::rest | Formula.Exp.UnOp (Invalid,_)::rest 
	| Formula.Exp.UnOp (Stack,_)::rest | Formula.Exp.UnOp (Static,_)::rest 
	| Formula.Exp.BinOp (_,UnOp(Base,_),_)::rest | Formula.Exp.BinOp (_,_,UnOp(Base,_))::rest 
	| Formula.Exp.BinOp (_,UnOp(Len,_),_)::rest | Formula.Exp.BinOp (_,_,UnOp(Len,_))::rest ->  prune_pure_form1 rest
        | first::rest -> first :: (prune_pure_form1 rest)

let test_sat {ctx=ctx; solv=solv; z3_names=_} form1 form2 =
  let query = (List.append (formula_to_solver ctx form1) (formula_to_solver ctx form2)) in
  if (Solver.check solv query)=UNSATISFIABLE then SatFail
  else
  if (List.length form2.sigma)>0 then NoFinish
  (* FINISH TRUE, return MISSING pure part (form2.pi) and FRAME (form1) *)
  (* All the equalities/disequalities/distances between variables from form1.pi should be added to the missing part, because 
     form1.pi is considered as axiom within each biabduction query. But these axioms may be missing in the MISS part of the state.
     The axioms freed(x) and invalid(x) from form1.pi are dropped, because a spatial predicate with x can be part of the MISS.
     The axioms base(x)[=,>,>=]y and len(x)[=,>,>=] from form1.pi are also droped, because they are not needed --- this is only 
     an optimization cutting useless conjuncts from MISS.
    *) 
  else Finish ({pi=(prune_pure_form1 form1.pi)@form2.pi; sigma=[]}, {pi=form1.pi; sigma=form1.sigma} )

(* main biabduction function *)
(* The result is:  "missing, frame, added_lvars, recorded split-rights" *)
type abduction_res =
| Bok of Formula.t * Formula.t * variable list * split_record list
| BFail

let rec biabduction solver form1 form2 pvars  =
  (* try the rules till an applicable if founded *)
  let rec try_rules todo=
    match todo with
    | (func_name,rule_arg,rule_name) :: rest ->
      (match (func_name solver form1 form2 rule_arg pvars) with
      | Apply (f1,f2,missing,n_lvars,split_rec) ->
        print_string (rule_name ^", "); flush stdout;
        Apply (f1,f2,missing,n_lvars,split_rec)
      | Fail ->
        try_rules rest
      )
    | [] -> Fail
  in
  (* First test SAT of form1 and form2.
     Postponing SAT to the end of biabduction may lead to hidden conflicts.
     The conflicts may be removed by application of a match rule.
   *) 
  (* Adding form1 into the solver is only a performance optimization. Its removal has no impact on correctness. *)
  Solver.push solver.solv;
  Solver.add solver.solv [Boolean.mk_and solver.ctx (formula_to_solver solver.ctx form1)];
  match (test_sat solver form1 form2) with
  | SatFail ->
    Solver.pop  solver.solv 1;
    prerr_endline "SAT fail (biabduction)"; BFail  
  | Finish (missing,frame) ->
    Solver.pop  solver.solv 1;
    print_endline "Finish true"; 
    Bok ( missing,frame, [], [])
  | NoFinish ->
  (* Here is a given list of possible rules and the order in which they are going to be applied *)
  (* Match4 and Split4 is applied only in case that nothing else can be applied *)
  let rules=[
    (try_match,0,"Match0");
    (try_split,0,"Split0");
    (*(try_match,1,"Match1");*)
    (*(try_split,1,"Split1");*)
    (try_match,2,"Match2");
    (try_split,2,"Split2");
    (try_match,3,"Match3");
    (*(try_learn_pointsto,1,"Learn1-Pointsto");*)
    (*(try_learn_slseg,1,"Learn1-Slseg");*)
    (try_learn_pointsto,3,"Learn3-Pointsto");
    (try_learn_slseg,2,"Learn3-Slseg");
    (try_match,4,"Match4");
    (try_split,4,"Split4");
  ] in
  match try_rules rules with
  | Apply (f1,f2,missing,n_lvars,rule_split_rec) ->
    Solver.pop  solver.solv 1;
    let split_rec_to_add=
    	match rule_split_rec with
    	| Record _ -> [rule_split_rec ]
    	| NoRecord -> []
    in
    (match biabduction solver f1 f2 pvars with
    | BFail -> BFail
    | Bok (miss,fr,l_vars,split_rec)-> 
    	Bok ({pi=(List.append missing.pi miss.pi);sigma=(List.append missing.sigma miss.sigma)}  ,fr, n_lvars@l_vars, split_rec_to_add@split_rec)
    )
  | Fail ->
    Solver.pop  solver.solv 1;
    raise_notrace NoApplicableRule




(*  Experiments
let solver = config_solver ()

check_match solver form1 0 pre_free 0 1

check_learn1 solver pre_free form2 1;;

try_learn1 solver form1 form2;;

find_match_ll solver form1 0 pre_free


*)

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
exception ShouldBeRefactoredToMakeExhaustive of unit
exception IllegalArgumentException of string
exception NoApplicableRule

(** result of the rule application
    form1 * form2 * M * added_local_vars
    or Fail
**)
type res =
  | Apply of Formula.t * Formula.t * Formula.t * variable list
  | Fail

let to_slseg_unsafe hpred = match hpred with
  | Hpointsto (_, _, _) -> raise (IllegalArgumentException "Received points-to assertion instead of list")
  | Slseg (a,b,l) -> (a,b,l)

let to_hpointsto_unsafe hpred = match hpred with
  | Slseg (_, _, _) -> raise (IllegalArgumentException "Received list instead of points-to assertion")
  | Hpointsto (a,l,b) -> (a,l,b)

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
    | Slseg (_,_,_) -> (find_z ctx solv z3_names form1 (z+1) form2 i2)
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
  | Slseg _ -> -1 (* Slseg is skipped, only Hpointsto is allowed in this function *)
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
		(Boolean.mk_eq ctx rhs lhs)
        | Slseg (a,_,_) -> 
      		let lhs=(expr_to_solver_only_exp ctx z3_names a) in
		(Boolean.mk_eq ctx
              	(Expr.mk_app ctx z3_names.base [rhs])
              	(Expr.mk_app ctx z3_names.base [lhs]))
        ) :: list_eq rest
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
  let common_part=match level with
  | 1 -> [Boolean.mk_and ctx (formula_to_solver ctx form1)] 
  | _ ->  [Boolean.mk_and ctx (formula_to_solver ctx form1); 
  	(Boolean.mk_and ctx (formula_to_solver ctx form2))]
  in
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
  match (get_index 0) with
  | (-1,-1) -> Solver.reset solver.solv; Fail
  | (-3,i2) -> Solver.reset solver.solv; 
    (* learn with level 3 *)
    Apply ( { sigma=form1.sigma; pi = form1.pi},
      (remove i2 form2),
      {sigma=[List.nth form2.sigma i2]; pi=[]},
      [])
  | (i1,i2) -> Solver.reset solver.solv;
    (* learn with level 1 *)
    let (y1,_,_) = to_hpointsto_unsafe (List.nth form1.sigma i1) in
    let (y2,_,_) = to_hpointsto_unsafe (List.nth form2.sigma i2) in

    Apply ( { sigma=form1.sigma; pi = (BinOp ( Pneq, y1,y2))::form1.pi},
      (remove i2 form2),
      {sigma=[List.nth form2.sigma i2]; pi=[]},
      [])

(**** LEARN - Slseg ****)
(* check whether we can apply learn on the form2.sigma[i2].
   The result is false: imposible
     true: possible
*)

let check_learn_slseg {ctx=ctx; solv=solv; z3_names=z3_names} form1 form2 i2 level =
  match (List.nth form2.sigma i2) with
  | Hpointsto (_,_,_) ->  false (* This funmction cover slseg learn only *)
  | Slseg (a,_,_) ->
    let rhs = (expr_to_solver_only_exp ctx z3_names a) in (* no negation -> no need to add existential quantification of undef *)
    (* create diffbase(rhs) and diffls(rhs) *)
    let rec list_eq sigma =
      match sigma with
      | [] -> []
      | first::rest ->
        (match first with
        | Hpointsto (a,_, _) -> 
        	let lhs=expr_to_solver_only_exp ctx z3_names a in
		(Boolean.mk_eq ctx
        	      (Expr.mk_app ctx z3_names.base [rhs])
	              (Expr.mk_app ctx z3_names.base [lhs]))
        | Slseg (a,_,_) -> 
        	let lhs=expr_to_solver_only_exp ctx z3_names a in
		(Boolean.mk_eq ctx rhs (lhs))
        ) :: list_eq rest
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
    | _ -> raise (TempExceptionBeforeApiCleanup "Should not be int result?")

(* try to apply learn rule for slseg *)
let try_learn_slseg solver form1 form2 level _=
  let ctx=solver.ctx in
  let common_part=match level with
  | 1 -> [Boolean.mk_and ctx (formula_to_solver ctx form1)]
  | 2 -> [(Boolean.mk_and ctx (formula_to_solver ctx form1));
          (Boolean.mk_and ctx (formula_to_solver ctx form2))] 
  | _ -> []
  in
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
  | -1 -> Solver.reset solver.solv; Fail
  | i -> Solver.reset solver.solv; Apply ( { sigma=form1.sigma; pi = form1.pi},
      (remove i form2),
      {sigma=[List.nth form2.sigma i]; pi=[]},
      [])

(************************************************************)
(******* SPLIT rules ******)

let check_split_left {ctx=ctx; solv=solv; z3_names=z3_names} form1 i1 form2 i2 level =
  let ff = Boolean.mk_false ctx in
  let ff_noZ3 = Exp.Const (Bool false) in
  let lhs,lhs_size,lhs_noZ3,lhs_size_noZ3 =
    match (List.nth form1.sigma i1) with
    | Hpointsto (a,s ,_) -> (expr_to_solver_only_exp ctx z3_names a),(expr_to_solver_only_exp ctx z3_names s),a,s
    | Slseg (_) -> ff,ff,ff_noZ3,ff_noZ3
  in
  let rhs,rhs_size,rhs_noZ3,rhs_size_noZ3 =
    match (List.nth form2.sigma i2) with
    | Hpointsto (a,s ,_) -> (expr_to_solver_only_exp ctx z3_names a),(expr_to_solver_only_exp ctx z3_names s),a,s
    | Slseg (_) -> ff,ff,ff_noZ3,ff_noZ3
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
        (BitVector.mk_sgt ctx lhs_size rhs_size)
        ] )
    ] in
    (Solver.check solv query)=UNSATISFIABLE 
    (* &&((Solver.check solv query_null)=UNSATISFIABLE || (lhs_dest = Undef)) *)(* here we may thing about better Undef recognition *)
  | 4 ->
    let query=[
      (BitVector.mk_sle ctx lhs rhs);
      (BitVector.mk_sge ctx (BitVector.mk_add ctx lhs lhs_size) (BitVector.mk_add ctx rhs rhs_size) );
      (BitVector.mk_sgt ctx lhs_size rhs_size) 
    ] in
    (Solver.check solv query)=SATISFIABLE 
      (*&& ((Solver.check solv query_null)=UNSATISFIABLE || (lhs_dest = Undef))*) (* here we may thing about better Undef recognition *)
  | _ -> raise (TempExceptionBeforeApiCleanup "Should not be int result?")

let check_split_right {ctx=ctx; solv=solv; z3_names=z3_names} form1 i1 form2 i2 level =
  let ff = Boolean.mk_false ctx in
  let ff_noZ3 = Exp.Const (Bool false) in
  let lhs,lhs_size,lhs_noZ3,lhs_size_noZ3 =
    match (List.nth form1.sigma i1) with
    | Hpointsto (a,s ,_) -> (expr_to_solver_only_exp ctx z3_names a),(expr_to_solver_only_exp ctx z3_names s),a,s
    | Slseg (_) -> ff,ff,ff_noZ3,ff_noZ3
  in
  let rhs,rhs_size,rhs_noZ3,rhs_size_noZ3 =
    match (List.nth form2.sigma i2) with
    | Hpointsto (a,s ,_) -> (expr_to_solver_only_exp ctx z3_names a),(expr_to_solver_only_exp ctx z3_names s),a,s
    | Slseg (_) -> ff,ff,ff_noZ3,ff_noZ3
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
        (BitVector.mk_slt ctx lhs_size rhs_size)
        ] )
     ] in
    (Solver.check solv query)=UNSATISFIABLE 
    (* && ((Solver.check solv query_null)=UNSATISFIABLE || (rhs_dest = Undef))*) (* here we may thing about better Undef recognition *)
  | 4 ->
    let query=[
      (BitVector.mk_sge ctx lhs rhs);
      (BitVector.mk_sle ctx (BitVector.mk_add ctx lhs lhs_size) (BitVector.mk_add ctx rhs rhs_size) );
      (BitVector.mk_slt ctx lhs_size rhs_size)
    ] in
    (Solver.check solv query)=SATISFIABLE 
    (* && ((Solver.check solv query_null)=UNSATISFIABLE || (rhs_dest = Undef)) *) (* here we may thing about better Undef recognition *)
  | _ -> raise (TempExceptionBeforeApiCleanup "Should not be int result?")


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
  Solver.add solver.solv common_part;
  let res= find_split_ll solver form1 0 form2 level in
  Solver.reset solver.solv; res



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
      (* Compute size of the first block -- Check form1 /\ form2 -> size_first=0 *)
      let size_first=
        let tmp_size_first=(Exp.BinOp (Pminus,x2,x1)) in
        let query = [ (Boolean.mk_and ctx (formula_to_solver ctx form1));
              (Boolean.mk_and ctx (formula_to_solver ctx form2));
              (expr_to_solver_only_exp ctx z3_names
                  (BinOp(Pneq, tmp_size_first, Exp.zero)))
            ]
        in
        if (Solver.check solv query)=UNSATISFIABLE
        then (Exp.zero)
        else tmp_size_first
      in
      let size_first_var = (get_fresh_var 1 variables) in
      let size_first_eq = (Exp.BinOp (Peq,Exp.Var size_first_var,size_first)) in
      (* Compute size of the last block -- Check form1 /\ form2 -> size_last=0 *)
      let size_last=
        let tmp_size_last=
          if size_first=(Exp.zero)
          then (Exp.BinOp(Pminus,s1,s2))
          else (Exp.BinOp(Pminus,s1,Exp.BinOp(Pplus,s2,size_first))) in
        let query = [ (Boolean.mk_and ctx (formula_to_solver ctx form1));
              (Boolean.mk_and ctx (formula_to_solver ctx form2));
              (expr_to_solver_only_exp ctx z3_names
                  (BinOp(Pneq,tmp_size_last,Exp.zero)))
            ]
        in
        if (Solver.check solv query)=UNSATISFIABLE then (Exp.zero)
        else tmp_size_last
      in
      let size_last_var = get_fresh_var (size_first_var+1) ([size_first_var]@variables) in
      let size_last_eq = (Exp.BinOp (Peq,Exp.Var size_last_var,size_last)) in
      (* pointer to the last segment *)
      let ptr_last=(Exp.BinOp(Pplus,x2,s2)) in
      let ptr_last_var = get_fresh_var (size_last_var+1) ([size_first_var; size_last_var]@variables) in
      let ptr_last_eq = (Exp.BinOp (Peq,Exp.Var ptr_last_var,ptr_last)) in
      (* destination of the split (null/undefined)*)
      let split_dest=
        let query_null=[ expr_to_solver_only_exp ctx z3_names (BinOp (Pneq,y1, Exp.zero));
          (Boolean.mk_and ctx (formula_to_solver ctx form1))
        ] in
        if (Solver.check solv query_null)=UNSATISFIABLE then Exp.zero else Exp.Undef
      in
      let sigma1_new,pi_tmp1, pi_tmp2, new_lvars= (* compute the splitted part of sigma and new pi*)
        if size_first=(Exp.zero) then
          [ Hpointsto (x1,s2,split_dest);
            Hpointsto (Exp.Var ptr_last_var,Exp.Var size_last_var,split_dest)],
           [ Exp.BinOp(Peq,x1,x2) ;
             BinOp ( Plesseq, s1, UnOp ( Len, x1));
             BinOp ( Peq, UnOp ( Base, x1), UnOp ( Base, Exp.Var ptr_last_var));
	     ptr_last_eq; size_last_eq],
           [ Exp.BinOp(Pless,s2,s1) ],
	   [ptr_last_var;size_last_var]
        else if  size_last=(Exp.zero) then
          [Hpointsto (x1,Exp.Var size_first_var,split_dest);
           Hpointsto (x2,s2,split_dest)],
           [Exp.BinOp(Peq,BinOp(Pplus,x2,s2),Exp.BinOp(Pplus,x1,s1));
             BinOp ( Plesseq, s1, UnOp ( Len, x1));
            BinOp ( Peq, UnOp ( Base, x1), UnOp ( Base, x2));
	    size_first_eq],
           [Exp.BinOp(Pless,s2,s1) ],
	   [size_first_var]
        else [Hpointsto (x1,Exp.Var size_first_var,split_dest);
          Hpointsto (x2,s2,split_dest);
          Hpointsto (Exp.Var ptr_last_var,Exp.Var size_last_var,split_dest)],
          [BinOp ( Plesseq, s1, UnOp ( Len, x1));
            BinOp ( Peq, UnOp ( Base, x1), UnOp ( Base, x2));
            BinOp ( Peq, UnOp ( Base, x1), UnOp ( Base, ptr_last));
	    size_first_eq; ptr_last_eq; size_last_eq],
          [Exp.BinOp(Plesseq,x1,x2); Exp.BinOp(Pless,s2,s1);Exp.BinOp(Plesseq,BinOp(Pplus,x2,s2),Exp.BinOp(Pplus,x1,s1)) ],
	  [size_first_var;ptr_last_var;size_last_var]
      in
      let new_pi=
        if (level=1) then pi_tmp1 (* form1 -> pi_tmp2, no need to add this information *)
        else pi_tmp1 @ pi_tmp2
      in
      Apply (  {sigma=sigma1_new@ (remove i1 form1).sigma; pi=form1.pi @ new_pi},
        form2,
        {sigma=[]; pi=new_pi},
        new_lvars)

    | 2 ->   (* split right *)
      (* Compute size of the first block -- Check form1 /\ form2 -> size_first=0 *)
      let size_first=
        let tmp_size_first=(Exp.BinOp (Pminus,x1,x2)) in
        let query = [ (Boolean.mk_and ctx (formula_to_solver ctx form1));
              (Boolean.mk_and ctx (formula_to_solver ctx form2));
              (expr_to_solver_only_exp ctx z3_names
                  (BinOp(Pneq,tmp_size_first,Exp.zero)))
            ]
        in
        if (Solver.check solv query)=UNSATISFIABLE
        then (Exp.zero)
        else tmp_size_first
      in
      let size_first_var = (get_fresh_var 1 variables) in
      let size_first_eq = (Exp.BinOp (Peq,Exp.Var size_first_var,size_first)) in
      (* Compute size of the last block -- Check form1 /\ form2 -> size_last=0 *)
      let size_last=
        let tmp_size_last=
          if size_first=(Exp.zero)
          then (Exp.BinOp(Pminus,s2,s1))
          else (Exp.BinOp(Pminus,s2,Exp.BinOp(Pplus,s1,size_first))) in
        let query = [ (Boolean.mk_and ctx (formula_to_solver ctx form1));
              (Boolean.mk_and ctx (formula_to_solver ctx form2));
              (expr_to_solver_only_exp ctx z3_names
                  (BinOp(Pneq,tmp_size_last,Exp.zero)))
            ]
        in
        if (Solver.check solv query)=UNSATISFIABLE
        then (Exp.zero)
        else tmp_size_last
      in
      let size_last_var = get_fresh_var (size_first_var+1) ([size_first_var]@variables) in
      let size_last_eq = (Exp.BinOp (Peq,Exp.Var size_last_var,size_last)) in
      (* pointer to the last block *)
      let ptr_last=(Exp.BinOp(Pplus,x1,s1)) in
      let ptr_last_var = get_fresh_var (size_last_var+1) ([size_first_var; size_last_var]@variables) in
      let ptr_last_eq = (Exp.BinOp (Peq,Exp.Var ptr_last_var,ptr_last)) in
      (* The RHS of the splitted points to can be null or undef *)
      let split_dest=
        let query_null=[ expr_to_solver_only_exp ctx z3_names (BinOp (Pneq,y2, Exp.zero));
          (Boolean.mk_and ctx (formula_to_solver ctx form2))
        ] in
        if (Solver.check solv query_null)=UNSATISFIABLE
        then Exp.zero
        else Exp.Undef
      in
      let sigma2_new,pi_tmp1,pi_tmp2,new_lvars= (* compute the splitted part of sigma *)
        if size_first=(Exp.zero) then
          [ Hpointsto (x1,s1,split_dest);
            Hpointsto (Exp.Var ptr_last_var,Exp.Var size_last_var,split_dest)],
           [ Exp.BinOp(Peq,x1,x2); BinOp ( Plesseq, s2, UnOp ( Len, x2));
	   ptr_last_eq; size_last_eq],
           [ Exp.BinOp(Pless,s1,s2) ],
	   [ptr_last_var; size_last_var]
        else if  size_last=(Exp.zero) then
          [Hpointsto (x2,Exp.Var size_first_var,split_dest);
           Hpointsto (x1,s1,split_dest)],
           [Exp.BinOp(Peq,BinOp(Pplus,x2,s2),Exp.BinOp(Pplus,x1,s1));
             BinOp ( Plesseq, s2, UnOp ( Len, x2));
            BinOp ( Peq, UnOp ( Base, x1), UnOp ( Base, x2));
	    size_first_eq],
           [Exp.BinOp(Pless,s1,s2) ],
	   [ size_first_var]
        else [Hpointsto (x2,Exp.Var size_first_var,split_dest);
          Hpointsto (x1,s1,split_dest);
          Hpointsto (Exp.Var ptr_last_var,Exp.Var size_last_var,split_dest)],
          [BinOp ( Plesseq, s2, UnOp ( Len, x2)); BinOp ( Peq, UnOp ( Base, x1), UnOp ( Base, x2));
	  ptr_last_eq; size_last_eq; size_first_eq ],
          [Exp.BinOp(Plesseq,x2,x1); Exp.BinOp(Pless,s1,s2);Exp.BinOp(Plesseq,BinOp(Pplus,x1,s1),Exp.BinOp(Pplus,x2,s2)) ],
	  [size_first_var;ptr_last_var;size_last_var ]
      in
      let new_pi=
        if (level=1) then pi_tmp1 (* form1 -> pi_tmp2, no need to add this information *)
        else pi_tmp1 @ pi_tmp2
      in

      Apply ({sigma=form1.sigma; pi=form1.pi @ new_pi},
        {sigma=sigma2_new@ (remove i2 form2).sigma; pi=form2.pi},
        {sigma=[]; pi=new_pi},
        new_lvars)
    | _ -> raise (TempExceptionBeforeApiCleanup "Should not be int result?")

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

  print_endline (lvariables_to_string evars);
  (* First all Slseg(x,y,_) are replaced by x=y --- i.e. empty list *)
  let rec remove_slseg_form2 f2 =
    match f2.sigma with
    | [] -> RemOk f2.pi
    | Hpointsto _ :: _ -> RemFail
    | Slseg (a,b,_) :: rest ->
      match (remove_slseg_form2 {pi=f2.pi; sigma=rest}) with
      | RemFail -> RemFail
      | RemOk f2_new -> RemOk (Exp.BinOp ( Peq, a, b):: f2_new)
  in
  match (remove_slseg_form2 form2) with
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
(**** MATCH Stack and Static pure predicates ****)
(* Find pair of points-to for match. Return (-1,-1) if unposibble *)

let check_match_onstack {ctx=ctx; solv=solv; z3_names=z3_names} form1 i1 form2 i2 level= 
  let ff = Boolean.mk_false ctx in
  let lhs_src,lhs_dest, lhs_flag =
    match (List.nth form1.pi i1) with
    | Exp.BinOp (op,a,b) ->
    	(match op with 
	| Stack -> (expr_to_solver_only_exp ctx z3_names a),(expr_to_solver_only_exp ctx z3_names b), 0 
	| Static -> (expr_to_solver_only_exp ctx z3_names a),(expr_to_solver_only_exp ctx z3_names b), 1
	| _ -> ff,ff,3
	)
    | _ -> ff,ff,3
  in
  let rhs_src,rhs_dest, rhs_flag =
    match (List.nth form2.pi i2) with
    | Exp.BinOp (op,a,b) ->
    	(match op with 
	| Stack ->  (expr_to_solver_only_exp ctx z3_names a),(expr_to_solver_only_exp ctx z3_names b),0
	| Static -> (expr_to_solver_only_exp ctx z3_names a),(expr_to_solver_only_exp ctx z3_names b),1
	| _ -> ff,ff,4
	)
    | _ -> ff,ff,4
  in
  (*if (lhs_src=ff)||(rhs_src=ff) *)
  if not (lhs_flag=rhs_flag) 
  then false
  else
  match level with
  | 1 ->
  	let query1 = [Boolean.mk_not ctx (Boolean.mk_eq ctx lhs_src rhs_src);
        	(Boolean.mk_and ctx (formula_to_solver ctx form1));
		(Boolean.mk_and ctx (formula_to_solver ctx form2))]
	in
  	(Solver.check solv query1)=UNSATISFIABLE
  | 2 ->
  	let query2 = [(Boolean.mk_eq ctx lhs_src rhs_src);
        	(Boolean.mk_and ctx (formula_to_solver ctx form1));
		(Boolean.mk_and ctx (formula_to_solver ctx form2))]
	in
	(lhs_dest=rhs_dest) &&((Solver.check solv query2)=SATISFIABLE)
  | 3 ->
  	let query1 = [Boolean.mk_not ctx (Boolean.mk_eq ctx lhs_dest rhs_dest);
        	(Boolean.mk_and ctx (formula_to_solver ctx form1))]
	in
  	let query2 = [(Boolean.mk_eq ctx lhs_src rhs_src);
        	(Boolean.mk_and ctx (formula_to_solver ctx form1));
		(Boolean.mk_and ctx (formula_to_solver ctx form2))]
	in
	((Solver.check solv query1)=UNSATISFIABLE) &&((Solver.check solv query2)=SATISFIABLE)
  | 4 ->
  	let query1 = [Boolean.mk_not ctx (Boolean.mk_eq ctx lhs_dest rhs_dest);
        	(Boolean.mk_and ctx (formula_to_solver ctx form1));
		(Boolean.mk_and ctx (formula_to_solver ctx form2))]
	in
  	let query2 = [(Boolean.mk_eq ctx lhs_src rhs_src);
        	(Boolean.mk_and ctx (formula_to_solver ctx form1));
		(Boolean.mk_and ctx (formula_to_solver ctx form2))]
	in
	((Solver.check solv query1)=UNSATISFIABLE) &&((Solver.check solv query2)=SATISFIABLE)
         
  | _ -> false


let rec find_match_onstack_ll solver form1 i1 form2 level  =
  let rec try_with_rhs i2 =
    if (List.length form2.pi) <= i2
    then -1
    else (if (check_match_onstack solver form1 i1 form2 i2 level)
      then i2
      else (try_with_rhs (i2+1)))
  in
  if (List.length form1.pi) <= i1
  then (-1,-1)
  else
    match (try_with_rhs 0) with
    | -1 -> (find_match_onstack_ll solver form1 (i1+1) form2 level)
    | x -> (i1,x)

let find_match_onstack solver form1 form2 level =
  find_match_onstack_ll solver form1 0 form2 level 

(* try to mathc stack and static predicates *)
let try_match_onstack solver form1 form2 level _  =
  let m=find_match_onstack solver form1 form2 level in
  match m with
  | (-1,-1) -> Fail
  | (i1,i2) -> print_endline ("Match onstack Apply "^(string_of_int i1)^" "^(string_of_int i2)) ;
	let nequiv a b = not (a=b) in
	let remove k form =
	    { sigma=form.sigma;
	      pi=List.filter (nequiv (List.nth form.pi k)) form.pi }
	in
	let f1,f2=(remove i1 form1), (remove i2 form2) in
	let x1,y1 =
	    match (List.nth form1.pi i1) with
	    | Exp.BinOp (_,a,b) -> a,b
	    | _ -> raise (TempExceptionBeforeApiCleanup "Should not be int result?")
	in
	let x2,y2 =
	    match (List.nth form2.pi i2) with
	    | Exp.BinOp (_,a,b) -> a,b
	    | _ -> raise (TempExceptionBeforeApiCleanup "Should not be int result?")
	in

	let x_eq=[(Exp.BinOp ( Peq, x1,x2))] in
        let y_eq=[(Exp.BinOp ( Peq, y1,y2))] in
      	match level with
	| 2 | 3 ->   Apply ( { sigma=f1.sigma; pi = x_eq @ f1.pi},
          f2,
          {sigma=[]; pi=x_eq},
          [])
      	| 1 | 4 ->   Apply ( { sigma=f1.sigma; pi = x_eq @ y_eq @ f1.pi},
          f2,
          {sigma=[]; pi=x_eq @ y_eq },
          [])
      	| _ ->  raise (TempExceptionBeforeApiCleanup "Should not be int result?")


  

(******************************************************************************)
(**** MATCH rules ****)
(* The level parameter gives the level of match, the only difference is in check_match function *)

(* Check whether match (of the given level) can be applied on i1^th pointsto on LHS and i2^th points-to on RHS *)
let check_match {ctx=ctx; solv=solv; z3_names=z3_names} form1 i1 form2 i2 level =
  let ff = Boolean.mk_false ctx in
  let ff_noZ3 = Exp.Const (Bool false)in
  let lhs_ll,lhs_noZ3,flag_l =
    match (List.nth form1.sigma i1) with
    | Hpointsto (a,_ ,_) -> (expr_to_solver_only_exp ctx z3_names a),a,0
    | Slseg (a,_,_) -> (expr_to_solver_only_exp ctx z3_names a),a,1
  in
  let lhs_size,lhs_size_noZ3 =
    match (List.nth form1.sigma i1) with
    | Hpointsto (_, s ,_) -> (expr_to_solver_only_exp ctx z3_names s),s
    | Slseg _ -> ff,ff_noZ3 (* we do not speak about sizes before the slseg is unfolded *)
  in
  let rhs_ll,rhs_noZ3,flag_r =
    match (List.nth form2.sigma i2) with
    | Hpointsto (a,_ ,_) -> (expr_to_solver_only_exp ctx z3_names a),a,0
    | Slseg (a,_,_) -> (expr_to_solver_only_exp ctx z3_names a),a,1
  in
  let rhs_size,rhs_size_noZ3 =
    match (List.nth form2.sigma i2) with
    | Hpointsto (_, s ,_) -> (expr_to_solver_only_exp ctx z3_names s),s
    | Slseg _ -> ff,ff_noZ3 (* we do not speak about sizes before the slseg is unfolded *)
  in
  (* Note that if one site contains list segment and the other one points-to then we compare bases
     within the SMT queries *)
  let lhs=if (flag_l+flag_r)=1
    then (Expr.mk_app ctx z3_names.base [lhs_ll])
    else lhs_ll
  in
  let rhs=if (flag_l+flag_r)=1
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
    then -1
    else (if (check_match solver form1 i1 form2 i2 level)
      then i2
      else (try_with_rhs (i2+1)))
  in
  if (List.length form1.sigma) <= i1
  then (-1,-1)
  else
    match (try_with_rhs 0) with
    | -1 -> (find_match_ll solver form1 (i1+1) form2 level)
    | x -> (i1,x)

let find_match solver form1 form2 level =
  let ctx=solver.ctx in
  let common_part=match level with
  | 1 | 3 -> [Boolean.mk_and ctx (formula_to_solver ctx form1)]
  | 2 | 4 -> [(Boolean.mk_and ctx (formula_to_solver ctx form1));
          (Boolean.mk_and ctx (formula_to_solver ctx form2))] 
  | _ -> []
  in
  Solver.add solver.solv common_part;
  let res=find_match_ll solver form1 0 form2 level in
  Solver.reset solver.solv; res



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

let rec apply_match solver i pred_type form1 form2 pvars =
  let nequiv a b = not (a=b) in
  let remove k form =
    { pi=form.pi;
      sigma=List.filter (nequiv (List.nth form.sigma k)) form.sigma }
  in
  match i with
  | (i1,i2) ->
    match pred_type with
    | 0 -> ApplyOK ((remove i1 form1), (remove i2 form2), [])
    | 1 -> let new_form2,new_lvars=unfold_predicate form2 i2 ((find_vars form1)@pvars) in
      ApplyOK (form1, new_form2, new_lvars)
    | 2 -> let new_form1,new_lvars=unfold_predicate form1 i1 ((find_vars form2)@pvars) in
      ApplyOK (new_form1, form2, new_lvars)
    | 3 ->
      let _,y1,ls1 = to_slseg_unsafe  (List.nth form1.sigma i1) in
      let _,y2,ls2 = to_slseg_unsafe (List.nth form2.sigma i2) in
      (*if (ls1=ls2) then *) (* Use this line to break the mutual recursion. *)
      if (check_lambda_entailment solver ls1 ls2)=1 then
        let lhs=(remove i1 form1) in
        let rhs_tmp=(remove i2 form2) in
        let rhs={sigma=(Slseg (y1,y2,ls2))::rhs_tmp.sigma; pi=rhs_tmp.pi} in
        ApplyOK (lhs, rhs, [])
	
      else  ApplyFail
    | _ -> raise (TempExceptionBeforeApiCleanup "Should not be int result?")


(* Try to apply match rule. The result is:
1:  form1 - the LHS formula with removed matched part and added equality x=y
  form2 - the RHS formula with removed matched part
  M - the learned part
2:  unfolded Slseg in form1/form2 and added equality x=y

*)
and try_match solver form1 form2 level pvars  =
  let m=find_match solver form1 form2 level in
  match m with
  | (-1,-1) -> Fail
  | (i1,i2) ->
    let x1,y1,type1,size1=match (List.nth form1.sigma i1) with
      | Hpointsto (a,size,b) -> (a,b,0,size)
      | Slseg (a,b,_) -> (a,b,2,Exp.Void) in
    let x2,y2,type2,size2=match (List.nth form2.sigma i2) with
      | Hpointsto (a,size,b) -> (a,b,0,size)
      | Slseg (a,b,_) -> (a,b,1,Exp.Void) in
    match apply_match solver (i1,i2) (type1+type2) form1 form2 pvars with
    | ApplyFail -> Fail
    | ApplyOK (f1,f2,added_lvars) ->
      (* x1 = x2 if equal predicate types match. Othervice base(x1) = base(x2) is added. *)
      let x_eq=if ((type1+type2)=0 || (type1+type2=3))
        then [(Exp.BinOp ( Peq, x1,x2))]
        else [(Exp.BinOp ( Peq, Exp.UnOp(Base,x1), Exp.UnOp(Base,x2)))]
      in
      (* y1 = y2 is added only if Hpointsto is mathced with Hpointsto *)
      let y_eq=if (type1+type2)=0 then [(Exp.BinOp ( Peq, y1,y2))] else [] in
      (* size1 = size2 is added if Hpointsto is mathced with Hpointsto *)
      let size_eq=if (type1+type2)=0 then [(Exp.BinOp ( Peq, size1,size2))] else [] in
      match level with
      | 1 ->   Apply ( { sigma=f1.sigma; pi = y_eq @ f1.pi},
          f2,
          {sigma=[]; pi=[]},
          added_lvars)
      | 0 | 3 ->   Apply ( { sigma=f1.sigma; pi = x_eq @ y_eq @ f1.pi},
          f2,
          {sigma=[]; pi=x_eq},
          added_lvars)
      | _ ->   Apply ( { sigma=f1.sigma; pi = x_eq @ y_eq @ size_eq @ f1.pi},
          f2,
          {sigma=[]; pi=x_eq @ size_eq},
          added_lvars)




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
		| _ -> raise (TempExceptionBeforeApiCleanup "Should not be int result?") (*{sigma=[];pi=[]}*)
	in
	let lambda1_new= rename_params lambda1.form lambda1.param new_params in
	let lambda2_new= rename_params lambda2.form lambda2.param new_params in
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
     (match (try_match solver form1 form2 1 []),(try_match solver form1 form2 2 []) with
     | Apply (f1,f2,_,_),_ ->
  		print_string "Match, "; flush stdout;
  		(entailment_ll solver f1 f2 evars)
     | Fail,Apply (f1,f2,_,_) ->
  		print_string "Match2, "; flush stdout;
  		(entailment_ll solver f1 f2 evars)
     | Fail,Fail -> false)
  | _ -> raise (TempExceptionBeforeApiCleanup "Should not be int result?")

and entailment solver form1 form2 evars=
  (* get fresh names for the evars to avoid conflicts in the entailment query *)
  let form1_s=Formula.simplify form1 evars in
  let form2_s=Formula.simplify form2 evars in
  (*print_string "XXXXXXXXXXXXXXXXXXXXXX\nFORM1: ";
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
  if res then print_endline "ENT VALID" else print_endline "ENT INVALID";
  res

(****************************************************)
(* MAIN biabduction procedure *)

(* Test SAT of (form1 /\ form2) and check finish *)
type sat_test_res =
| Finish of Formula.t * Formula.t
| NoFinish
| SatFail

let test_sat {ctx=ctx; solv=solv; z3_names=_} form1 form2 =
  let query = (List.append (formula_to_solver ctx form1) (formula_to_solver ctx form2)) in
  if (Solver.check solv query)=UNSATISFIABLE then SatFail
  else
  if (List.length form2.sigma)>0 then NoFinish
  (* FINISH TRUE, return MISSING pure part (form2.pi) and FRAME (form1) *)
  else Finish ({pi=form1.pi@form2.pi; sigma=[]}, {pi=form1.pi; sigma=form1.sigma} )

(* main biabduction function *)
(* The result is:  "missing, frame, added_lvars" *)
type abduction_res =
| Bok of Formula.t * Formula.t * variable list
| BFail

let rec biabduction solver form1 form2 pvars =
  (* try the rules till an applicable if founded *)
  let rec try_rules todo=
    match todo with
    | (func_name,rule_arg,rule_name) :: rest ->
      (match (func_name solver form1 form2 rule_arg pvars) with
      | Apply (f1,f2,missing,n_lvars) ->
        print_string (rule_name ^", "); flush stdout;
        Apply (f1,f2,missing,n_lvars)
      | Fail ->
        try_rules rest
      )
    | [] -> Fail
  in
  let rules_onstack=[
    (try_match_onstack,1,"Match-Stack/Static-1");
    (try_match_onstack,2,"Match-Stack/Static-2");
  ] in
  (* First test SAT of form1 and form2.
     Postponing SAT to the end of biabduction may lead to hidden conflicts.
     The conflicts may be removed by application of a match rule.
     The Finish true is aplied only if Match-onstack can not be applied
   *)
  match (test_sat solver form1 form2),(try_rules rules_onstack) with
  | SatFail, _ ->
    prerr_endline "SAT fail (biabduction)"; BFail  
  | Finish (missing,frame), Fail ->
    print_endline "Finish true"; Bok ( missing,frame, [])
  | _, Apply (f1,f2,missing,n_lvars) ->
    (match biabduction solver f1 f2 pvars with
    | BFail -> BFail
    | Bok (miss,fr,l_vars)-> Bok ({pi=(List.append missing.pi miss.pi);sigma=(List.append missing.sigma miss.sigma)}  ,fr, n_lvars@l_vars)
    )
  | NoFinish, Fail ->
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
    (try_learn_pointsto,1,"Learn1-Pointsto");
    (try_learn_slseg,1,"Learn1-Slseg");
    (try_learn_pointsto,3,"Learn3-Pointsto");
    (try_learn_slseg,2,"Learn3-Slseg");
    (try_match,4,"Match4");
    (try_split,4,"Split4");
  ] in
  match try_rules rules with
  | Apply (f1,f2,missing,n_lvars) ->
    (match biabduction solver f1 f2 pvars with
    | BFail -> BFail
    | Bok (miss,fr,l_vars)-> Bok ({pi=(List.append missing.pi miss.pi);sigma=(List.append missing.sigma miss.sigma)}  ,fr, n_lvars@l_vars)
    )
  | Fail ->
    raise NoApplicableRule




(*  Experiments
let solver = config_solver ()

check_match solver form1 0 pre_free 0 1

check_learn1 solver pre_free form2 1;;

try_learn1 solver form1 form2;;

find_match_ll solver form1 0 pre_free

*)

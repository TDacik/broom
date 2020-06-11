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


(**** MATCH rules ****)
(* The level parameter gives the level of match, the only difference is in check_match function *)

(* Check whether match (of the given level) can be applied on i1^th pointsto on LHS and i2^th points-to on RHS *)
let check_match ctx solv z3_names form1 i1 form2 i2 level =
  let ff = Boolean.mk_false ctx in
  let lhs_ll,flag_l =
    match (List.nth form1.sigma i1) with
    | Hpointsto (a,_ ,_) -> (expr_to_solver ctx z3_names a),0
    | Slseg (a,_,_) -> (expr_to_solver ctx z3_names a),1
  in
  let lhs_size =
    match (List.nth form1.sigma i1) with
    | Hpointsto (_, s ,_) -> (expr_to_solver ctx z3_names s)
    | Slseg _ -> ff (* we do not speak about sizes before the slseg is unfolded *)
  in
  let rhs_ll,flag_r =
    match (List.nth form2.sigma i2) with
    | Hpointsto (a,_ ,_) -> (expr_to_solver ctx z3_names a),0
    | Slseg (a,_,_) -> (expr_to_solver ctx z3_names a),1
  in
  let rhs_size =
    match (List.nth form2.sigma i2) with
    | Hpointsto (_, s ,_) -> (expr_to_solver ctx z3_names s)
    | Slseg _ -> ff (* we do not speak about sizes before the slseg is unfolded *)
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
  | 1 ->
    let query_size =
      if ((lhs_size=ff)||(rhs_size=ff)) then true
      else
        let qq1 =[
          Boolean.mk_not ctx (Boolean.mk_eq ctx lhs_size rhs_size);
            (Boolean.mk_and ctx (formula_to_solver ctx form1)) ]
        in
      ((Solver.check solv qq1)=UNSATISFIABLE)
    in
    let query1 =
      [Boolean.mk_not ctx (Boolean.mk_eq ctx lhs rhs);
        (Boolean.mk_and ctx (formula_to_solver ctx form1))
      ]
    in
    query_size
    && ((Solver.check solv query1)=UNSATISFIABLE)
  | 2 ->
    let query_size =
      if ((lhs_size=ff)||(rhs_size=ff)) then true
      else
        let qq =[
          Boolean.mk_not ctx (Boolean.mk_eq ctx lhs_size rhs_size);
          (Boolean.mk_and ctx (formula_to_solver ctx form1));
          (Boolean.mk_and ctx (formula_to_solver ctx form2))
        ] in
      (Solver.check solv qq)=UNSATISFIABLE
    in
    let query =
      [Boolean.mk_not ctx (Boolean.mk_eq ctx lhs rhs);
        (Boolean.mk_and ctx (formula_to_solver ctx form1));
        (Boolean.mk_and ctx (formula_to_solver ctx form2))
      ]
    in
    query_size
    && ((Solver.check solv query)=UNSATISFIABLE)
  | 3 ->
    let query_size =
      if ((lhs_size=ff)||(rhs_size=ff)) then true
      else
        let qq1 =[
          Boolean.mk_not ctx (Boolean.mk_eq ctx lhs_size rhs_size);
            (Boolean.mk_and ctx (formula_to_solver ctx form1)) ]
        in
      ((Solver.check solv qq1)=UNSATISFIABLE)
    in
    let query1=[(Boolean.mk_and ctx (formula_to_solver ctx form1));
        (Boolean.mk_and ctx (formula_to_solver ctx form2));
        (Boolean.mk_eq ctx lhs rhs)
      ]
    in
    let query2=[Boolean.mk_not ctx (Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [lhs]) (Expr.mk_app ctx z3_names.base [rhs]));
        (Boolean.mk_and ctx (formula_to_solver ctx form1))
      ]
    in
    query_size
    && ((Solver.check solv query1)=SATISFIABLE) && ((Solver.check solv query2)=UNSATISFIABLE)
  | 4 ->
    let query_size =
      if ((lhs_size=ff)||(rhs_size=ff)) then true
      else
        let qq =[
          Boolean.mk_not ctx (Boolean.mk_eq ctx lhs_size rhs_size);
          (Boolean.mk_and ctx (formula_to_solver ctx form1));
          (Boolean.mk_and ctx (formula_to_solver ctx form2))
        ] in
      (Solver.check solv qq)=UNSATISFIABLE
    in
    let query=[(Boolean.mk_and ctx (formula_to_solver ctx form1));
        (Boolean.mk_and ctx (formula_to_solver ctx form2));
        (Boolean.mk_eq ctx lhs rhs)
      ]
    in
    query_size && ((Solver.check solv query)=SATISFIABLE)
  | _ -> false

(* Find pair of points-to for match. Return (-1,-1) if unposibble *)
let rec find_match_ll ctx solv z3_names form1 i1 form2 level=
  let (*rec*) try_with_rhs i2 =
    if (List.length form2.sigma) <= i2
    then -1
    else (if (check_match ctx solv z3_names form1 i1 form2 i2 level)
      then i2
      else -1)
  in
  if (List.length form1.sigma) <= i1
  then (-1,-1)
  else
    match (try_with_rhs 0) with
    | -1 -> (find_match_ll ctx solv z3_names form1 (i1+1) form2 level)
    | x -> (i1,x)

let find_match ctx solv z3_names form1 form2 level =
  find_match_ll ctx solv z3_names form1 0 form2 level


(* apply the match rule to i=(i1,i2)
   pred_type=0 --- pointsto x pointsto
   pred_type=1 --- pointsto x Slseg
   pred_type=2 --- Slseg x pointsto
   pred_type=3 --- Slseg x Slseg
*)
type apply_match_res =
| ApplyOK of Formula.t * Formula.t * variable list
| ApplyFail


let apply_match i pred_type form1 form2 gvars =
  let nequiv a b = not (a=b) in
  let remove k form =
    { pi=form.pi;
      sigma=List.filter (nequiv (List.nth form.sigma k)) form.sigma }
  in
  match i with
  | (i1,i2) ->
    match pred_type with
    | 0 -> ApplyOK ((remove i1 form1), (remove i2 form2), [])
    | 1 -> let new_form2,new_lvars=unfold_predicate form2 i2 ((find_vars form1)@gvars) in
      ApplyOK (form1, new_form2, new_lvars)
    | 2 -> let new_form1,new_lvars=unfold_predicate form1 i1 ((find_vars form2)@gvars) in
      ApplyOK (new_form1, form2, new_lvars)
    | 3 ->
      let _,y1,ls1 = to_slseg_unsafe  (List.nth form1.sigma i1) in
      let _,y2,ls2 = to_slseg_unsafe (List.nth form2.sigma i2) in
      if (ls1=ls2) then (* FIXME: This is ugly hack. Should be replaced by entailment check ls1 |-ls2 *)
        let lhs=(remove i1 form1) in
        let rhs_tmp=(remove i2 form2) in
        let rhs={sigma=(Slseg (y1,y2,ls2))::rhs_tmp.sigma; pi=rhs_tmp.pi} in
        ApplyOK (lhs, rhs, [])

      else ApplyFail
    | _ -> raise (TempExceptionBeforeApiCleanup "Should not be int result?")


(* Try to apply match rule. The result is:
1:  form1 - the LHS formula with removed matched part and added equality x=y
  form2 - the RHS formula with removed matched part
  M - the learned part
2:  unfolded Slseg in form1/form2 and added equality x=y
*)
let try_match ctx solv z3_names form1 form2 level gvars =
  let m=find_match ctx solv z3_names form1 form2 level in
  match m with
  | (-1,-1) -> Fail
  | (i1,i2) ->
    let x1,y1,type1,size1=match (List.nth form1.sigma i1) with
      | Hpointsto (a,size,b) -> (a,b,0,size)
      | Slseg (a,b,_) -> (a,b,2,Exp.Void) in
    let x2,y2,type2,size2=match (List.nth form2.sigma i2) with
      | Hpointsto (a,size,b) -> (a,b,0,size)
      | Slseg (a,b,_) -> (a,b,1,Exp.Void) in
    match apply_match (i1,i2) (type1+type2) form1 form2 gvars with
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
      | 3 ->   Apply ( { sigma=f1.sigma; pi = x_eq @ y_eq @ f1.pi},
          f2,
          {sigma=[]; pi=x_eq},
          added_lvars)
      | _ ->   Apply ( { sigma=f1.sigma; pi = x_eq @ y_eq @ size_eq @ f1.pi},
          f2,
          {sigma=[]; pi=x_eq @ size_eq},
          added_lvars)

(**** LEARN - pointsto ****)

(* let x be: form2.sigma[i2]=x->_
  we know that x!= y for all y->_ \in form1.sigma
  now find a z->_ in form1.sigma such that base(z) = base(x) is valid *)
let rec find_z ctx solv z3_names form1 z form2 i2 =
  if (List.length form1.sigma) <= z
    then -1
  else
  let (a, _, _) = to_hpointsto_unsafe (List.nth form2.sigma i2) in (* SIZE missing *) (* RHS can be Hpointsto only *)
  let rhs = expr_to_solver ctx z3_names a in
  match (List.nth form1.sigma z) with
    | Slseg (_,_,_) -> (find_z ctx solv z3_names form1 (z+1) form2 i2)
    | Hpointsto (a,_, _) ->
    let lhs= (expr_to_solver ctx z3_names a) in (* SIZE missing *)
    let query1= [ Boolean.mk_not ctx (
      Boolean.mk_eq ctx (Expr.mk_app ctx z3_names.base [lhs]) (Expr.mk_app ctx z3_names.base [rhs]));
      (Boolean.mk_not ctx (Boolean.mk_eq ctx lhs rhs));
      (Boolean.mk_and ctx (formula_to_solver ctx form1))
      ]
    in
    if ((Solver.check solv query1)=UNSATISFIABLE) then z
    else find_z ctx solv z3_names form1 (z+1) form2 i2

(* check whether we can apply learn on the form2.sigma[i2].
   The result is -1: imposible
        0...k: the index of "z" (if level=1)
     -3: possible (if level=3)
*)
let check_learn_pointsto ctx solv z3_names form1 form2 i2 level =
  match (List.nth form2.sigma i2) with
  | Slseg _ -> -1 (* Slseg is skipped, only Hpointsto is allowed in this function *)
  | Hpointsto (a,_,_) ->
    let rhs = (expr_to_solver ctx z3_names a) in
    (* create list of equalities between form2.sigma[i2] and all items in form1.sigma *)
    let rec list_eq pointsto_list =
      match pointsto_list with
      | [] -> []
      | first::rest ->
        (match first with
        | Hpointsto (a,_, _) -> (Boolean.mk_eq ctx rhs (expr_to_solver ctx z3_names a))
        | Slseg (a,_,_) -> (Boolean.mk_eq ctx
              (Expr.mk_app ctx z3_names.base [rhs])
              (Expr.mk_app ctx z3_names.base [expr_to_solver ctx z3_names a]))
        ) :: list_eq rest
    in
    let query = match (list_eq form1.sigma) with
      | [] -> [ (Boolean.mk_and ctx (formula_to_solver ctx form1));
          (Boolean.mk_and ctx (formula_to_solver ctx form2)) ]
      | a -> [ (Boolean.mk_not ctx (Boolean.mk_or ctx a));
          (Boolean.mk_and ctx (formula_to_solver ctx form1));
          (Boolean.mk_and ctx (formula_to_solver ctx form2)) ]
    in
    match level with
    | 1 ->   if ((Solver.check solv query)=SATISFIABLE) then
        find_z ctx solv z3_names form1 0 form2 i2
      else -1
    | 3 -> if ((Solver.check solv query)=SATISFIABLE) then -3 else -1
    | _ -> -1


(* try to apply learn1 rule for pointsto *)
let try_learn_pointsto ctx solv z3_names form1 form2 level _ =
  (* first find index of the rule on RHS, which can be learned on LHS *)
  let rec get_index i =
    if (List.length form2.sigma) <= i
    then (-1,-1)
    else
      let res=check_learn_pointsto ctx solv z3_names form1 form2 i level in
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
  | (-1,-1) -> Fail
  | (-3,i2) -> (* learn with level 3 *)
    Apply ( { sigma=form1.sigma; pi = form1.pi},
      (remove i2 form2),
      {sigma=[List.nth form2.sigma i2]; pi=[]},
      [])
  | (i1,i2) -> (* learn with level 1 *)
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

let check_learn_slseg ctx solv z3_names form1 form2 i2 level =
  match (List.nth form2.sigma i2) with
  | Hpointsto (_,_,_) ->  false (* This funmction cover slseg learn only *)
  | Slseg (a,_,_) ->
    let rhs = (expr_to_solver ctx z3_names a) in
    (* create diffbase(rhs) and diffls(rhs) *)
    let rec list_eq sigma =
      match sigma with
      | [] -> []
      | first::rest ->
        (match first with
        | Hpointsto (a,_, _) -> (Boolean.mk_eq ctx
              (Expr.mk_app ctx z3_names.base [rhs])
              (Expr.mk_app ctx z3_names.base [expr_to_solver ctx z3_names a]))
        | Slseg (a,_,_) -> (Boolean.mk_eq ctx rhs (expr_to_solver ctx z3_names a))
        ) :: list_eq rest
    in
    match level with
    | 1 -> (match  (list_eq form1.sigma) with
      | [] -> false (* learn1 can not be applied with empty sigma on LHS *)
      | a ->
        let query = [ (Boolean.mk_and ctx (formula_to_solver ctx form1));
           (Boolean.mk_or ctx a)]
        in
        (Solver.check solv query)=UNSATISFIABLE
      )
    | 2 ->   let query =
        match (list_eq form1.sigma) with
        | [] -> [(Boolean.mk_and ctx (formula_to_solver ctx form1));
          (Boolean.mk_and ctx (formula_to_solver ctx form2)) ]
        | a ->   [ (Boolean.mk_not ctx (Boolean.mk_or ctx a));
          (Boolean.mk_and ctx (formula_to_solver ctx form1));
          (Boolean.mk_and ctx (formula_to_solver ctx form2)) ]
      in
      (Solver.check solv query)=SATISFIABLE
    | _ -> raise (TempExceptionBeforeApiCleanup "Should not be int result?")

(* try to apply learn rule for slseg *)
let try_learn_slseg ctx solv z3_names form1 form2 level _=
  (* first find index of the rule on RHS, which can be learned on LHS *)
  let rec get_index i =
    if (List.length form2.sigma) <= i
    then -1
    else
      if (check_learn_slseg ctx solv z3_names form1 form2 i level)
      then i
      else get_index (i+1)
  in
  let nequiv a b = not (a=b) in
  let remove k form =
    { pi=form.pi;
      sigma=List.filter (nequiv (List.nth form.sigma k)) form.sigma }
  in
  match (get_index 0) with
  | -1 -> Fail
  | i -> Apply ( { sigma=form1.sigma; pi = form1.pi},
      (remove i form2),
      {sigma=[List.nth form2.sigma i]; pi=[]},
      [])

(************************************************************)
(******* SPLIT rules ******)

let check_split_left ctx solv z3_names form1 i1 form2 i2 level =
  let ff = Boolean.mk_false ctx in
  let lhs,lhs_size,lhs_dest =
    match (List.nth form1.sigma i1) with
    | Hpointsto (a,s ,b) -> (expr_to_solver ctx z3_names a),(expr_to_solver ctx z3_names s),b
    | Slseg (_) -> ff,ff,Exp.Const (Int Int64.zero)
  in
  let rhs,rhs_size =
    match (List.nth form2.sigma i2) with
    | Hpointsto (a,s ,_) -> (expr_to_solver ctx z3_names a),(expr_to_solver ctx z3_names s)
    | Slseg (_) -> ff,ff
  in
  if ((lhs=ff)||(rhs=ff))
  then false
  else
  let query_null=[ expr_to_solver ctx z3_names (BinOp (Pneq, lhs_dest, Const (Int Int64.zero)));
    (Boolean.mk_and ctx (formula_to_solver ctx form1))
    ] in
  match level with
  | 1 ->
    let query=[
      Boolean.mk_not ctx (
        Boolean.mk_and ctx [
        (BitVector.mk_sle ctx lhs rhs);
        (BitVector.mk_sge ctx (BitVector.mk_add ctx lhs lhs_size) (BitVector.mk_add ctx rhs rhs_size) );
        (BitVector.mk_sgt ctx lhs_size rhs_size)
        ] );
      (Boolean.mk_and ctx (formula_to_solver ctx form1))
    ] in
    (Solver.check solv query)=UNSATISFIABLE &&
    ((Solver.check solv query_null)=UNSATISFIABLE || (lhs_dest = Undef)) (* here we may thing about better Undef recognition *)
  | 2 ->
    let query=[
      Boolean.mk_not ctx (
        Boolean.mk_and ctx [
        (BitVector.mk_sle ctx lhs rhs);
        (BitVector.mk_sge ctx (BitVector.mk_add ctx lhs lhs_size) (BitVector.mk_add ctx rhs rhs_size) );
        (BitVector.mk_sgt ctx lhs_size rhs_size)
        ] );
      (Boolean.mk_and ctx (formula_to_solver ctx form1));
      (Boolean.mk_and ctx (formula_to_solver ctx form2))
    ] in
    (Solver.check solv query)=UNSATISFIABLE &&
    ((Solver.check solv query_null)=UNSATISFIABLE || (lhs_dest = Undef)) (* here we may thing about better Undef recognition *)
  | 4 ->
    let query=[
      (BitVector.mk_sle ctx lhs rhs);
      (BitVector.mk_sge ctx (BitVector.mk_add ctx lhs lhs_size) (BitVector.mk_add ctx rhs rhs_size) );
      (BitVector.mk_sgt ctx lhs_size rhs_size);
      (Boolean.mk_and ctx (formula_to_solver ctx form1));
      (Boolean.mk_and ctx (formula_to_solver ctx form2))
    ] in
    (Solver.check solv query)=SATISFIABLE &&
      ((Solver.check solv query_null)=UNSATISFIABLE || (lhs_dest = Undef)) (* here we may thing about better Undef recognition *)
  | _ -> raise (TempExceptionBeforeApiCleanup "Should not be int result?")

let check_split_right ctx solv z3_names form1 i1 form2 i2 level =
  let ff = Boolean.mk_false ctx in
  let lhs,lhs_size =
    match (List.nth form1.sigma i1) with
    | Hpointsto (a,s ,_) -> (expr_to_solver ctx z3_names a),(expr_to_solver ctx z3_names s)
    | Slseg (_) -> ff,ff
  in
  let rhs,rhs_size,rhs_dest =
    match (List.nth form2.sigma i2) with
    | Hpointsto (a,s ,b) -> (expr_to_solver ctx z3_names a),(expr_to_solver ctx z3_names s), b
    | Slseg (_) -> ff,ff, Exp.Const  (Int Int64.zero)
  in
  if ((lhs=ff)||(rhs=ff))
  then false
  else
  (* we should check that the destination is NULL or UNDEF *)
  let query_null=[ expr_to_solver ctx z3_names (BinOp (Pneq, rhs_dest, Const (Int Int64.zero)));
    (Boolean.mk_and ctx (formula_to_solver ctx form2))
    ] in
  match level with
  | 1 ->
    let query=[
      Boolean.mk_not ctx (
        Boolean.mk_and ctx [
        (BitVector.mk_sge ctx lhs rhs);
        (BitVector.mk_sle ctx (BitVector.mk_add ctx lhs lhs_size) (BitVector.mk_add ctx rhs rhs_size) );
        (BitVector.mk_slt ctx lhs_size rhs_size)
        ] );
      (Boolean.mk_and ctx (formula_to_solver ctx form1))
    ] in
    (Solver.check solv query)=UNSATISFIABLE &&
    ((Solver.check solv query_null)=UNSATISFIABLE || (rhs_dest = Undef)) (* here we may thing about better Undef recognition *)
  | 2 ->
    let query=[
      Boolean.mk_not ctx (
        Boolean.mk_and ctx [
        (BitVector.mk_sge ctx lhs rhs);
        (BitVector.mk_sle ctx (BitVector.mk_add ctx lhs lhs_size) (BitVector.mk_add ctx rhs rhs_size) );
        (BitVector.mk_slt ctx lhs_size rhs_size)
        ] );
      (Boolean.mk_and ctx (formula_to_solver ctx form1));
      (Boolean.mk_and ctx (formula_to_solver ctx form2))
    ] in
    (Solver.check solv query)=UNSATISFIABLE &&
    ((Solver.check solv query_null)=UNSATISFIABLE || (rhs_dest = Undef)) (* here we may thing about better Undef recognition *)
  | 4 ->
    let query=[
      (BitVector.mk_sge ctx lhs rhs);
      (BitVector.mk_sle ctx (BitVector.mk_add ctx lhs lhs_size) (BitVector.mk_add ctx rhs rhs_size) );
      (BitVector.mk_slt ctx lhs_size rhs_size);
      (Boolean.mk_and ctx (formula_to_solver ctx form1));
      (Boolean.mk_and ctx (formula_to_solver ctx form2))
    ] in
    (Solver.check solv query)=SATISFIABLE &&
      ((Solver.check solv query_null)=UNSATISFIABLE || (rhs_dest = Undef)) (* here we may thing about better Undef recognition *)
  | _ -> raise (TempExceptionBeforeApiCleanup "Should not be int result?")


let rec find_split_ll ctx solv z3_names form1 i1 form2 level=
  let (*rec*) try_with_rhs i2 =
    if (List.length form2.sigma) <= i2
    then -1,-1
    else (if (check_split_left ctx solv z3_names form1 i1 form2 i2 level)
      then i2,1
      else ( if (check_split_right ctx solv z3_names form1 i1 form2 i2 level)
        then i2,2
        else -1,-1))
  in
  if (List.length form1.sigma) <= i1
  then (-1,-1,-1)
  else
    match (try_with_rhs 0) with
    | -1,_ -> (find_split_ll ctx solv z3_names form1 (i1+1) form2 level)
    | x,lr -> (i1,x,lr)

let find_split ctx solv z3_names form1 form2 level =
  find_split_ll ctx solv z3_names form1 0 form2 level


let try_split ctx solv z3_names form1 form2 level _ =
  let m=find_split ctx solv z3_names form1 form2 level in
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
              (expr_to_solver ctx z3_names
                  (BinOp(Pneq, tmp_size_first, Const (Int Int64.zero))))
            ]
        in
        if (Solver.check solv query)=UNSATISFIABLE
        then (Exp.Const (Int Int64.zero))
        else tmp_size_first
      in
      (* Compute size of the last block -- Check form1 /\ form2 -> size_last=0 *)
      let size_last=
        let tmp_size_last=
          if size_first=(Const (Int Int64.zero))
          then (Exp.BinOp(Pminus,s1,s2))
          else (Exp.BinOp(Pminus,s1,Exp.BinOp(Pplus,s2,size_first))) in
        let query = [ (Boolean.mk_and ctx (formula_to_solver ctx form1));
              (Boolean.mk_and ctx (formula_to_solver ctx form2));
              (expr_to_solver ctx z3_names
                  (BinOp(Pneq,tmp_size_last,Const (Int Int64.zero))))
            ]
        in
        if (Solver.check solv query)=UNSATISFIABLE then (Exp.Const (Int Int64.zero))
        else tmp_size_last
      in
      let ptr_last=(Exp.BinOp(Pplus,x2,s2)) in
      let split_dest=
        let query_null=[ expr_to_solver ctx z3_names (BinOp (Pneq,y1, Const (Int Int64.zero)));
          (Boolean.mk_and ctx (formula_to_solver ctx form1))
        ] in
        if (Solver.check solv query_null)=UNSATISFIABLE then Exp.Const (Int Int64.zero) else Exp.Undef
      in
      let sigma1_new,pi_tmp1, pi_tmp2= (* compute the splitted part of sigma and new pi*)
        if size_first=(Const (Int Int64.zero)) then
          [ Hpointsto (x1,s2,split_dest);
            Hpointsto (ptr_last,size_last,split_dest)],
           [ Exp.BinOp(Peq,x1,x2) ;
             BinOp ( Plesseq, s1, UnOp ( Len, x1));
             BinOp ( Peq, UnOp ( Base, x1), UnOp ( Base, ptr_last))],
           [ Exp.BinOp(Pless,s2,s1) ]
        else if  size_last=(Const (Int Int64.zero)) then
          [Hpointsto (x1,size_first,split_dest);
           Hpointsto (x2,s2,split_dest)],
           [Exp.BinOp(Peq,BinOp(Pplus,x2,s2),Exp.BinOp(Pplus,x1,s1));
             BinOp ( Plesseq, s1, UnOp ( Len, x1));
            BinOp ( Peq, UnOp ( Base, x1), UnOp ( Base, x2))],
           [Exp.BinOp(Pless,s2,s1) ]
        else [Hpointsto (x1,size_first,split_dest);
          Hpointsto (x2,s2,split_dest);
          Hpointsto (ptr_last,size_last,split_dest)],
          [BinOp ( Plesseq, s1, UnOp ( Len, x1));
            BinOp ( Peq, UnOp ( Base, x1), UnOp ( Base, x2));
            BinOp ( Peq, UnOp ( Base, x1), UnOp ( Base, ptr_last))],
          [Exp.BinOp(Plesseq,x1,x2); Exp.BinOp(Pless,s2,s1);Exp.BinOp(Plesseq,BinOp(Pplus,x2,s2),Exp.BinOp(Pplus,x1,s1)) ]
      in
      let new_pi=
        if (level=1) then pi_tmp1 (* form1 -> pi_tmp2, no need to add this information *)
        else pi_tmp1 @ pi_tmp2
      in
      Apply (  {sigma=sigma1_new@ (remove i1 form1).sigma; pi=form1.pi @ new_pi},
        form2,
        {sigma=[]; pi=new_pi},
        [])

    | 2 ->   (* split right *)
      (* Compute size of the first block -- Check form1 /\ form2 -> size_first=0 *)
      let size_first=
        let tmp_size_first=(Exp.BinOp (Pminus,x1,x2)) in
        let query = [ (Boolean.mk_and ctx (formula_to_solver ctx form1));
              (Boolean.mk_and ctx (formula_to_solver ctx form2));
              (expr_to_solver ctx z3_names
                  (BinOp(Pneq,tmp_size_first,Const (Int Int64.zero))))
            ]
        in
        if (Solver.check solv query)=UNSATISFIABLE
        then (Exp.Const (Int Int64.zero))
        else tmp_size_first
      in
      (* Compute size of the last block -- Check form1 /\ form2 -> size_last=0 *)
      let size_last=
        let tmp_size_last=
          if size_first=(Const (Int Int64.zero))
          then (Exp.BinOp(Pminus,s2,s1))
          else (Exp.BinOp(Pminus,s2,Exp.BinOp(Pplus,s1,size_first))) in
        let query = [ (Boolean.mk_and ctx (formula_to_solver ctx form1));
              (Boolean.mk_and ctx (formula_to_solver ctx form2));
              (expr_to_solver ctx z3_names
                  (BinOp(Pneq,tmp_size_last,Const (Int Int64.zero))))
            ]
        in
        if (Solver.check solv query)=UNSATISFIABLE
        then (Exp.Const (Int Int64.zero))
        else tmp_size_last
      in
      let ptr_last=(Exp.BinOp(Pplus,x1,s1)) in
      let split_dest=
        let query_null=[ expr_to_solver ctx z3_names (BinOp (Pneq,y2, Const (Int Int64.zero)));
          (Boolean.mk_and ctx (formula_to_solver ctx form2))
        ] in
        if (Solver.check solv query_null)=UNSATISFIABLE
        then Exp.Const (Int Int64.zero)
        else Exp.Undef
      in
      let sigma2_new,pi_tmp1,pi_tmp2= (* compute the splitted part of sigma *)
        if size_first=(Const (Int Int64.zero)) then
          [ Hpointsto (x1,s1,split_dest);
            Hpointsto (ptr_last,size_last,split_dest)],
           [ Exp.BinOp(Peq,x1,x2); BinOp ( Plesseq, s2, UnOp ( Len, x2)) ],
           [ Exp.BinOp(Pless,s1,s2) ]
        else if  size_last=(Const (Int Int64.zero)) then
          [Hpointsto (x2,size_first,split_dest);
           Hpointsto (x1,s1,split_dest)],
           [Exp.BinOp(Peq,BinOp(Pplus,x2,s2),Exp.BinOp(Pplus,x1,s1));
             BinOp ( Plesseq, s2, UnOp ( Len, x2));
            BinOp ( Peq, UnOp ( Base, x1), UnOp ( Base, x2))],
           [Exp.BinOp(Pless,s1,s2) ]
        else [Hpointsto (x2,size_first,split_dest);
          Hpointsto (x1,s1,split_dest);
          Hpointsto (ptr_last,size_last,split_dest)],
          [BinOp ( Plesseq, s2, UnOp ( Len, x2)); BinOp ( Peq, UnOp ( Base, x1), UnOp ( Base, x2))],
          [Exp.BinOp(Plesseq,x2,x1); Exp.BinOp(Pless,s1,s2);Exp.BinOp(Plesseq,BinOp(Pplus,x1,s1),Exp.BinOp(Pplus,x2,s2)) ]
      in
      let new_pi=
        if (level=1) then pi_tmp1 (* form1 -> pi_tmp2, no need to add this information *)
        else pi_tmp1 @ pi_tmp2
      in

      Apply ({sigma=form1.sigma; pi=form1.pi @ new_pi},
        {sigma=sigma2_new@ (remove i2 form2).sigma; pi=form2.pi},
        {sigma=[]; pi=new_pi},
        [])
    | _ -> raise (TempExceptionBeforeApiCleanup "Should not be int result?")

(****************************************************)
(* Test SAT of (form1 /\ form2) and check finish *)
type sat_test_res =
| Finish of Formula.t
| NoFinish
| SatFail

let test_sat ctx solv __names form1 form2 =
  let query = (List.append (formula_to_solver ctx form1) (formula_to_solver ctx form2)) in
  if (Solver.check solv query)=UNSATISFIABLE then SatFail
  else
  if (List.length form2.sigma)>0 then NoFinish
  else Finish {pi=form1.pi; sigma=form1.sigma} (* return FRAME, pi may be not empty --- To be Checked *)

(* main biabduction function *)
(* The result is:  "missing, frame, added_lvars" *)

type abduction_res =
| Bok of Formula.t * Formula.t * variable list
| BFail

let rec biabduction ctx solv z3_names form1 form2 gvars =
  (* First test SAT of form1 and form2.
     Postponing SAT to the end of biabduction may lead to hidden conflicts.
     The conflicts may be removed by application of a match rule.
   *)
  match (test_sat ctx solv z3_names form1 form2) with
  | SatFail ->
    print_string "SAT fail"; BFail
  | Finish frame -> print_string "Finish true, "; Bok ( {pi=[];sigma=[]} ,frame, [])
  | NoFinish ->
  (* Here is a given list of possible rules and the order in which they are going to be applied *)
  let rules=[
    (try_match,1,"Match1");
    (try_split,1,"Split1");
    (try_match,2,"Match2");
    (try_split,2,"Split2");
    (try_match,3,"Match3");
    (try_learn_pointsto,1,"Learn1-Pointsto");
    (try_learn_slseg,1,"Learn1-Slseg");
    (try_match,4,"Match4");
    (try_split,4,"Split4");
    (try_learn_pointsto,3,"Learn3-Pointsto");
    (try_learn_slseg,2,"Learn3-Slseg")
  ] in
  (* try the rules till an applicable if founded *)
  let rec try_rules todo=
    match todo with
    | (func_name,rule_arg,rule_name) :: rest ->
      (match (func_name ctx solv z3_names form1 form2 rule_arg gvars) with
      | Apply (f1,f2,missing,n_lvars) ->
        print_string (rule_name ^", ");
        Apply (f1,f2,missing,n_lvars)
      | Fail ->
        try_rules rest
      )
    | [] -> Fail
  in
  match try_rules rules with
  | Apply (f1,f2,missing,n_lvars) ->
    (match biabduction ctx solv z3_names f1 f2 gvars with
    | BFail -> BFail
    | Bok (miss,fr,l_vars)-> Bok ({pi=(List.append missing.pi miss.pi);sigma=(List.append missing.sigma miss.sigma)}  ,fr, n_lvars@l_vars)
    )
  | Fail ->
    print_string "No applicable rule"; BFail


(****************************************************)
(* check entailment using match1 rules *)

type entailment_slseg_remove =
| RemOk of Formula.pi
| RemFail

let (*rec*) check_entailment_finish ctx solv __names form1 form2 evars=
  if (List.length form1.sigma)>0 then -1
  else
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
    let f2=Boolean.mk_and ctx (formula_to_solver ctx {pi=x; sigma=[]}) in
    let f2_q=match evars_z3 with
      | [] -> f2
      | ev -> Quantifier.expr_of_quantifier
        (Quantifier.mk_exists_const ctx ev f2 (Some 1) [] []
        (Some (Symbol.mk_string ctx "Q1")) (Some (Symbol.mk_string ctx "skid1"))) in
    let query = (Boolean.mk_not ctx f2_q) :: (formula_to_solver ctx form1) in
    if (Solver.check solv query)=UNSATISFIABLE then 1
    else 0

let rec entailment_ll ctx solv z3_names form1 form2 evars=
(* check entailment between form1 and form2 using match1 rules *)
  match (check_entailment_finish ctx solv z3_names form1 form2 evars) with
  | 0 -> false
  | 1 -> true
  | -1 ->
     (match (try_match ctx solv z3_names form1 form2 1 []) with
     | Apply (f1,f2,_,_) ->
  print_string "Match, ";
  (entailment_ll ctx solv z3_names f1 f2 evars)
     | Fail -> false)
  | _ -> raise (TempExceptionBeforeApiCleanup "Should not be int result?")

let (*rec*) entailment ctx solv z3_names form1 form2 evars=
  (* get fresh names for the evars to avoid conflicts in the entailment query *)
  let conflicts1=find_vars form1 in
  let form2_rename,evars2=match (rename_ex_variables form2 evars conflicts1) with
    | f -> f
  in
  let conflicts2=find_vars form2_rename in
  let form1_rename,evars1=match (rename_ex_variables form1 evars conflicts2) with
    | f -> f
  in
  let query=(formula_to_solver ctx form1_rename) @ (formula_to_solver ctx form2_rename) in
  (Solver.check solv query)=SATISFIABLE && (entailment_ll ctx solv z3_names form1_rename form2_rename (evars@evars1@evars2))



(*  Experiments
let cfg = [("model", "true"); ("proof", "false")]
let ctx = (mk_context cfg)
let solv = (Solver.mk_solver ctx None)
let z3_names=get_sl_functions_z3 ctx


check_match ctx solv z3_names form1 0 pre_free 0 1

check_learn1 ctx solv z3_names pre_free form2 1;;

try_learn1 ctx solv z3_names form1 form2;;

find_match_ll ctx solv z3_names form1 0 pre_free

*)

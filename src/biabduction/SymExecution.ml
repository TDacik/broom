open State
open Formula
open Z3
open Z3wrapper

type contract_app_res =
  | CAppOk of State.t
  | CAppFail

(* apply contract,
   * we assume that contract variables are not used within the state s,
   * only the program variables may appear in both contract and state, they are used as anchors
*)
let apply_contract ctx solv z3_names state c =
  match (Abduction.biabduction ctx solv z3_names state.act c.Contract.lhs) with
  | BFail -> CAppFail
  | Bok  (miss, fr, l_vars) ->
    let missing= {pi=state.miss.pi @ miss.pi; sigma=state.miss.sigma @ miss.sigma } in
    let actual= {pi=fr.pi @ c.rhs.pi; sigma= fr.sigma @ c.rhs.sigma } in

    CAppOk {miss=missing; act=actual; lvars=(state.lvars @ l_vars)  }

(* to avoid conflicts, we rename the contract variables, which appear in state *)
let rec rename_contract_vars_ll state c seed =
  let svars=join_list_unique (find_vars state.act) (find_vars state.miss) in
  let cvars=join_list_unique (find_vars c.Contract.lhs) (find_vars c.rhs) in
  let mem x l =
    let eq y= (x=y) in
    List.exists eq l
  in
  let rec get_fresh_var s confl =
    if (mem s confl)
    then get_fresh_var (s+1) confl
    else s
  in
  (* let rec substitutelist newv oldv l =
    match l with
    | [] -> []
    | first::rest ->
      if first=oldv
      then newv::(substitutelist newv oldv rest)
      else first::(substitutelist newv oldv rest)
  in *)
  (* contract variable is only second *)
  let rec substitute_varmap newv oldv l =
    match l with
    | [] -> []
    | (a,b)::rest ->
      if b=oldv
      then (a,newv)::(substitute_varmap newv oldv rest)
      else (a,b)::(substitute_varmap newv oldv rest)
  in
  match c.cvars with
  | 0 -> c
  | n -> let new_var = get_fresh_var seed (svars @ cvars) in
         let new_c={ Contract.lhs=substitute_vars new_var n c.lhs;
           rhs=substitute_vars new_var n c.rhs;
           cvars=(n-1);
           pvarmap=substitute_varmap new_var n c.pvarmap;
         } in
         (rename_contract_vars_ll state new_c (new_var+1) )


exception State_lhs_contains_forbidden_vars

(* RENAMING AFTER CONTRACT APPLICATION
   for each tuple (a,b) \in pvarmap
  * rename all occurences of a by a fresh lvar
  * rename all occurences of b by a
*)
let rec post_contract_application_vars state pvarmap seed=
  let mem l x =
    let eq y= (x=y) in
    List.exists eq l
  in
  let rec get_fresh_var s confl=
    if (mem confl s)
    then get_fresh_var (s+1) confl
    else s
  in
  match pvarmap with
  | [] -> state
  | (a,b)::rest ->
    if mem (find_vars state.miss) b
    then raise State_lhs_contains_forbidden_vars
    else
      let new_var=get_fresh_var seed ((find_vars state.miss)@(find_vars state.act)) in
      let tmp_act=substitute_vars new_var a state.act in
      let new_act=substitute_vars a b tmp_act in
      let new_lvars=
        let eq y= not (b=y) in
        List.filter eq state.lvars
      in
      let new_state={ act=new_act;
          miss= state.miss;
          lvars=new_lvars @ [new_var];
        } in
      (post_contract_application_vars new_state rest (new_var+1))

(* REMOVE THE FREED PARTS *)

exception Conflict_between_freed_and_slseg

let remove_freed_parts ctx solv z3_names form =
  let rec get_freed pure =
    match pure with
    | [] -> []
    | first:: rest ->
      match first with
      | Exp.UnOp (Freed,a) -> a:: (get_freed rest)
      | _ -> get_freed rest
  in
  let rec cut_freed pure =
    match pure with
    | [] -> []
    | first:: rest ->
      match first with
      | Exp.UnOp (Freed,_) ->  cut_freed rest
      | _ -> first :: (cut_freed rest)
  in
  let form_z3=formula_to_solver ctx {sigma=form.sigma; pi=cut_freed form.pi} in
  let check_eq_base_ll a base =
    let query=Boolean.mk_not ctx
      (Boolean.mk_eq ctx
        (expr_to_solver ctx z3_names base)
        (Expr.mk_app ctx z3_names.base [(expr_to_solver ctx z3_names a)])
      )
      :: form_z3
    in
    (Solver.check solv query)=UNSATISFIABLE
  in
  let rec check_eq_base a base_list =
    match base_list with
    | [] -> false
    | first::rest -> (check_eq_base_ll a first) || (check_eq_base a rest)
  in
  let rec cut_spatial sp base_list=
    match sp with
    | [] -> []
    | Hpointsto (a,b,c) :: rest ->
      if (check_eq_base a base_list)
      then (cut_spatial rest base_list)
      else Hpointsto (a,b,c) ::(cut_spatial rest base_list)
    | Slseg (a,b,c) :: rest ->
      if (check_eq_base a base_list)
      then raise Conflict_between_freed_and_slseg
      else Slseg (a,b,c) ::(cut_spatial rest base_list)

  in

  {sigma=(cut_spatial form.sigma (get_freed form.pi)) ; pi=form.pi}


(* after contract application do the following thing
  1: rename variables according to pvarmap
  2: for each freed(x) predicate in pure part remove the spatial predicates
     with the equal base
*)
let post_contract_application state ctx solv z3_names pvarmap =
  let step1=post_contract_application_vars state pvarmap 1 in
  {miss=step1.miss; act=(remove_freed_parts ctx solv z3_names step1.act); lvars=step1.lvars}

(* Do
   1) rename conflicting contract variables
   2) apply the contract using biabduction
   3) apply post contract renaming
*)
let contract_application ctx solv z3_names state c =
  let c_rename = rename_contract_vars_ll state c 1 in
  match (apply_contract ctx solv z3_names state c_rename) with
  | CAppFail -> CAppFail
  | CAppOk s_applied ->
    CAppOk (post_contract_application s_applied ctx solv z3_names c_rename.pvarmap)

(********************************************)
(* Experiments

let pre_move = {
    sigma = [ Hpointsto (Var 1, ptr_size, Var 3) ];
    pi = [ BinOp ( Peq, Var 1, Var 2332) ]
}
let post_move = {
    sigma = [ Hpointsto (Var 1, ptr_size, Var 3) ];
    pi = [ BinOp ( Peq, Var 3, Var 2) ]
}

let c_move={lhs=pre_move; rhs=post_move; cvars=3; pvarmap=[(2332,2)]}

let pre_change = {
    sigma = [ Hpointsto (Var 1, ptr_size, Var 2) ];
    pi = [ BinOp ( Peq, Var 1, Var 2332);
     BinOp ( Peq, Var 1,  UnOp ( Base, Var 1)) ]
}
let post_change = {
    sigma = [ Hpointsto (Var 1, ptr_size, Var 3) ];
    pi = [ BinOp ( Peq, Var 1, Var 2332);
     BinOp ( Peq, Var 1,  UnOp ( Base, Var 1))  ]
}

let c_change={lhs=pre_change; rhs=post_change; cvars=3; pvarmap=[]}

let c_free={lhs=Formula.pre_free; rhs=Formula.post_free; cvars=0; pvarmap=[]};;
let s={miss={sigma=[];pi=[]};  act=Formula.form1; lvars=[1;2]}

let s1={miss={sigma=[];pi=[]};  act=Formula.form5; lvars=[1;2;4]}

open Z3
open Z3wrapper
let cfg = [("model", "true"); ("proof", "false")]
let ctx = (mk_context cfg)
let solv = (Solver.mk_solver ctx None)
let z3_names=get_sl_functions_z3 ctx

--------------------------------------------------

let tmp=match contract_application ctx solv z3_names s1 c_move with
| CAppOk x -> x;;

let s2=simplify tmp;;

*)

module FExp = Formula.Exp
open Formula
open Z3wrapper

exception Conflict_between_freed_and_slseg

let cut_freed_and_invalid_parts ?(replaced=false) {ctx=ctx; solv=solv; z3_names=z3_names} form_z3 form freed_list invalid_list =
    let check_eq_base_ll a base =
      let query=Z3.Boolean.mk_not ctx
        (Z3.Boolean.mk_eq ctx
          (Z3.Expr.mk_app ctx z3_names.base [(expr_to_solver_only_exp ctx z3_names base)])
          (Z3.Expr.mk_app ctx z3_names.base [(expr_to_solver_only_exp ctx z3_names a)])
        )
        :: form_z3
      in
      (Z3.Solver.check solv query)=UNSATISFIABLE
    in
    let rec check_eq_base a base_list =
      match base_list with
      | [] -> false
      | first::rest -> (check_eq_base_ll a first) || (check_eq_base a rest)
    in
    let rec cut_spatial sp base_list  =
      match sp with
      | [] -> []
      | Hpointsto (a,b,c) :: rest ->
        if (check_eq_base a base_list)
        then (cut_spatial rest base_list )
        else Hpointsto (a,b,c) ::(cut_spatial rest base_list )
      | Slseg (a,b,c) :: rest ->
        if (check_eq_base a base_list)
        then raise Conflict_between_freed_and_slseg
        else Slseg (a,b,c) ::(cut_spatial rest base_list )
    in
    (* cat all "Stack(x,_)" predicates, where base(x) is part of base_list
       if replaced is true, add Invalid(x) *)
    let rec cut_pure pure base_list =
      match pure with
      | [] -> []
      | FExp.BinOp (Stack,a,b) :: rest -> (
          if (check_eq_base a base_list)
          then (if replaced
            then FExp.UnOp (Invalid,a) ::(cut_pure rest base_list)
            else (cut_pure rest base_list) )
          else FExp.BinOp (Stack,a,b) ::(cut_pure rest base_list)
      )
      | first::rest -> first :: (cut_pure rest base_list)
    in

    {sigma=(cut_spatial form.sigma (freed_list @ invalid_list));
     pi=(cut_pure form.pi invalid_list)}

(* freed are on heap / invalid are on stack *)
let remove_freed_and_invalid_parts solver form =
  let get_freed pure =
    let get_base exp =
      match exp with
      | FExp.UnOp (Freed,a) -> Some a
      | _ -> None
    in
    List.filter_map get_base pure
  in
  let get_invalid pure =
    let get_base exp =
      match exp with
      | FExp.UnOp (Invalid,a) -> Some a
      | _ -> None
    in
    List.filter_map get_base pure
  in
  let rec cut_freed_invalid pure =
    match pure with
    | [] -> []
    | first:: rest ->
      match first with
      | FExp.UnOp (Freed,_) | FExp.UnOp (Invalid,_) ->  cut_freed_invalid rest
      | _ -> first :: (cut_freed_invalid rest)
  in

  let freed_list = get_freed form.pi in
  let invalid_list = get_invalid form.pi in
  let form_z3 = formula_to_solver solver.ctx {sigma=form.sigma; pi=cut_freed_invalid form.pi} in
  cut_freed_and_invalid_parts solver form_z3 form freed_list invalid_list

let remove_stack ?(replaced=false) solver form =
  let get_stack pure =
    let get_base exp =
      match exp with
      | FExp.BinOp (Stack,a,_) -> Some a
      | _ -> None
    in
    List.filter_map get_base pure
  in
  let invalid_list = get_stack form.pi in
  let form_z3 = formula_to_solver solver.ctx form in
  cut_freed_and_invalid_parts ~replaced solver form_z3 form [] invalid_list

(* because abduction doing something weird, when is used only remove_stack *)
let remove_stack2 ?(replaced=false) solver form lvars =
  let get_stack pure =
    let get_base exp =
      match exp with
      | FExp.BinOp (Stack,Var a,Var b) when List.mem a lvars && List.mem b lvars -> Some (Exp.Var a)
      | _ -> None
    in
    List.filter_map get_base pure
  in
  let invalid_list = get_stack form.pi in
  let form_z3=formula_to_solver solver.ctx form in
  cut_freed_and_invalid_parts ~replaced solver form_z3 form [] invalid_list

(** [subformula vars form] returns
    flag if something was removed from spatial part
    list of all variables that may be in subformula
    a subformula that contains clauses with variables from [vars] and related
    variables to them
    [form] - expect satisfiable formula only
    [vars] - list of FExp, but expect CVar and Var only *)
let rec subformula solver vars f =
  match vars with
  | [] ->
    (* print_string ("END_SUBFORMULA: "); print_endline (to_string f); *)
    (* remove stack and static predicates from f *)
    let get_ignore pure =
      let get_base exp =
        match exp with
        | FExp.BinOp (Stack,a,_) -> Some a
        | BinOp (Static,a,_) -> Some a
        | _ -> None
      in
      List.filter_map get_base pure
    in
    let ignore_list = get_ignore f.pi in
    let form_z3 = formula_to_solver solver.ctx f in
    let f_new = cut_freed_and_invalid_parts solver form_z3 {sigma = f.sigma; pi = []} [] ignore_list in
    let removed_sigma = if (f_new.sigma = []) then false else true in
    (removed_sigma,vars,empty)
  | _ ->
    let (new_vars,new_f) = subformula_only vars f in
    let (flag,tl_vars,tl_f) = subformula solver new_vars (diff f new_f) in
    let all_vars = (vars @ tl_vars) in
    (* print_string ("subformula:"^CL.Util.list_to_string (Exp.to_string) vars ^ "\n");
    print_string (CL.Util.list_to_string (Exp.to_string) all_vars ^ "ALL\n"); *)
    (flag,all_vars, disjoint_union new_f tl_f)

exception RemovedSpatialPartFromMiss

(* [substate fixed_vars state] contains in miss and curr only clauses with
   variables from [fixed_vars] and related variables
   [state] - expect satisfiable state only
   [fixed_vars] - list of FExp, but expect CVar and Var only

   miss_vars = fixed_vars + related
   curr_vars = fixed_vars + related from miss + related from curr *)
(* TODO errors/warnings handling *)
let substate solver fixed_vars state =
  let get_lvar var =
    match var with
    | FExp.Var v when (List.mem v state.State.lvars) -> Some v
    | _ -> None
  in
  (* print_string ("\n" ^ CL.Util.list_to_string (Exp.to_string ~lvars:state.lvars) fixed_vars ^ "FIXED\n"); *)
  let (miss_removed_sigma,miss_vars,new_miss) =
    subformula solver fixed_vars state.miss in
  if (miss_removed_sigma)
  then raise RemovedSpatialPartFromMiss;
  (* print_string ("\n" ^ CL.Util.list_to_string (Formula.Exp.to_string ~lvars:state.lvars) miss_vars ^ "AFTER MISS\n"); *)
  let (curr_removed_sigma,curr_vars,new_curr) =
    subformula solver miss_vars state.curr in
  if (curr_removed_sigma)
  then (if (Unix.isatty Unix.stderr) (* TODO more general *)
    then prerr_endline "\027[1;35m!!! MEMORY LEAK\027[0m"
    else prerr_endline "!!! MEMORY LEAK");
    (* print_string ("\n" ^ CL.Util.list_to_string (Formula.Exp.to_string ~lvars:state.lvars) curr_vars ^ "AFTER curr\n"); *)
  let all_vars = List.filter_map get_lvar (curr_vars) in
  {State.miss = new_miss;
   curr = new_curr;
   lvars = all_vars}


(* SIMPLIFY *)

(** [formula_simplify2 solver fixed_vars form] is global simplify function,
    returns true, if something was removed from sigma and simplified formula
    [fixed_vars] - variables can't be removed
    [form] - expect satisfiable formula only *)
let formula solver fixed_vars form =
  let fixed_vars_exp = FExp.get_list_vars fixed_vars in
  let (removed_sigma,all_vars,subf) = subformula solver fixed_vars_exp form in
  let evars = CL.Util.list_diff (Exp.get_list_uids all_vars) fixed_vars in
  (removed_sigma, Formula.remove_equiv_vars fixed_vars evars subf)

(* fixed_vars - variables can't be removed
   state - expect satisfiable state only *)
(* FIXME may be more variables in lvars than are in state *)
let state solver fixed_vars state =
  let fixed_vars_exp = FExp.get_list_vars fixed_vars in
  let rems = State.remove_equiv_vars fixed_vars state.State.lvars state in
  let subs = substate solver fixed_vars_exp rems in
  (* (find_vars rems.miss) @ (find_vars rems.curr) in *)
  subs

(*
 *  Copyright (C) Broom team
 *
 *  This file is part of Broom.
 *
 *  Broom is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  Broom is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <https://www.gnu.org/licenses/>.
 *)

module FExp = Formula.Exp
open Formula
open Z3wrapper
open Z3

exception Conflict_between_freed_and_lseg

let cut_freed_and_invalid_parts ?(replaced=false) solver form_z3 form freed_list invalid_list =
    let rec check_eq_bases a base_list =
      match base_list with
      | [] -> false
      | first::rest ->
        (Z3wrapper.check_eq_base solver form_z3 a first) ||
        (check_eq_bases a rest)
    in
    let rec cut_spatial sp base_list  =
      match sp with
      | [] -> []
      | Hpointsto (a,b,c) :: rest ->
        if (check_eq_bases a base_list)
        then (cut_spatial rest base_list )
        else Hpointsto (a,b,c) ::(cut_spatial rest base_list )
      | Slseg (a,b,c,shared) :: rest ->
        if (check_eq_bases a base_list)
        then raise Conflict_between_freed_and_lseg
        else Slseg (a,b,c,shared) ::(cut_spatial rest base_list )
      | Dlseg (a,b,c,d,l,shared) :: rest ->
        if ((check_eq_bases a base_list) || (check_eq_bases c base_list))
        then raise Conflict_between_freed_and_lseg
        else Dlseg (a,b,c,d,l,shared) ::(cut_spatial rest base_list )
    in
    (* cat all "Stack(x)" predicates, where base(x) is part of base_list
       if replaced is true, add Invalid(x) *)
    let rec cut_pure pure base_list =
      match pure with
      | [] -> []
      | FExp.UnOp (Stack,a) :: rest -> (
          if (check_eq_bases a base_list)
          then (if replaced
            then FExp.UnOp (Invalid,a) ::(cut_pure rest base_list)
            else (cut_pure rest base_list) )
          else FExp.UnOp (Stack,a) ::(cut_pure rest base_list)
      )
      | first::rest -> first :: (cut_pure rest base_list)
    in
    Z3.Solver.push solver.solv;
    Z3.Solver.add solver.solv form_z3;
    let res={sigma=(cut_spatial form.sigma (freed_list @ invalid_list));
          pi=(cut_pure form.pi invalid_list)} in
    Z3.Solver.pop solver.solv 1; res

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
      | FExp.UnOp (Stack,a) -> Some a
      | _ -> None
    in
    List.filter_map get_base pure
  in
  let invalid_list = get_stack form.pi in
  let form_z3 = formula_to_solver solver.ctx form in
  cut_freed_and_invalid_parts ~replaced solver form_z3 form [] invalid_list

(*  [subformula solver vars form] returns
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
        | FExp.UnOp (Stack,a) -> Some a
        | UnOp (Static,a) -> Some a
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
exception RemovedSpatialPartFromCurr


(* [substate solver fixed_vars state] contains in miss and curr only clauses
   with variables from [fixed_vars] and related variables
   [state] - expect satisfiable state only
   [fixed_vars] - list of FExp, but expect CVar and Var only

   miss_vars = fixed_vars + related
   curr_vars = fixed_vars + related from miss + related from curr *)
(* TODO errors/warnings handling *)
let substate solver fixed_vars state loc =
  let get_lvar var =
    match var with
    | FExp.Var v when (List.mem v state.State.lvars) -> Some v
    | _ -> None
  in
  (* print_string ("\n" ^ CL.Util.list_to_string (Exp.to_string ~lvars:state.lvars) fixed_vars ^ "FIXED\n"); *)
  let (miss_removed_sigma,miss_vars,new_miss) =
    subformula solver fixed_vars state.miss in
  if (miss_removed_sigma)
  then raise_notrace RemovedSpatialPartFromMiss;
  (* print_string ("\n" ^ CL.Util.list_to_string (Formula.Exp.to_string ~lvars:state.lvars) miss_vars ^ "AFTER MISS\n"); *)
  let (curr_removed_sigma,curr_vars,new_curr) =
    subformula solver miss_vars state.curr in
  if (curr_removed_sigma) then (
    if Config.memory_leaks_as_errors ()
    then raise_notrace RemovedSpatialPartFromCurr
    else (Config.prerr_warn "memory leak" loc) );
    (* print_string ("\n" ^ CL.Util.list_to_string (Formula.Exp.to_string ~lvars:state.lvars) curr_vars ^ "AFTER curr\n"); *)
  let all_vars = List.filter_map get_lvar (curr_vars) in
  {State.miss = new_miss;
   curr = new_curr;
   lvars = all_vars;
   through_loop = state.through_loop}


(* SIMPLIFY *)

(** [formula solver fixed_vars form] is global simplify function,
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
(* TODO if found invalid(var) put var into lvars and remove from fixed_vars *)
let state solver fixed_vars state loc =
  let fixed_vars_exp = FExp.get_list_vars fixed_vars in
  let rems = State.remove_equiv_vars fixed_vars state.State.lvars state in
  let subs = substate solver fixed_vars_exp rems loc in
  (* (find_vars rems.miss) @ (find_vars rems.curr) in *)
  subs


(** prune useless lsegs using Z3 solver and call Formula.simplify ***)  
let rec prune_empty_lsegs_ll sigma solver =
	match sigma with
	| [] -> ([],[])
	| Slseg(a,b,l,shared)::rest -> 
		let rest_sigma,rest_pi=prune_empty_lsegs_ll rest solver in
		let a_solv=expr_to_solver_only_exp solver.ctx solver.z3_names a in
		let b_solv=expr_to_solver_only_exp solver.ctx solver.z3_names b in
		let query=[Boolean.mk_not solver.ctx (Boolean.mk_eq solver.ctx a_solv b_solv)] in
		if (Solver.check solver.solv query)=UNSATISFIABLE
		then rest_sigma, Exp.BinOp(Peq, a, b):: rest_pi
		else  Slseg(a,b,l,shared) :: rest_sigma, rest_pi

	| Dlseg(a,b,c,d,l,shared)::rest -> 
		(* a=d or b=c ---> the list must be empty *)
		let rest_sigma,rest_pi=prune_empty_lsegs_ll rest solver in
		let a_solv=expr_to_solver_only_exp solver.ctx solver.z3_names a in
		let b_solv=expr_to_solver_only_exp solver.ctx solver.z3_names b in
		let c_solv=expr_to_solver_only_exp solver.ctx solver.z3_names c in
		let d_solv=expr_to_solver_only_exp solver.ctx solver.z3_names d in
		let query=[Boolean.mk_not solver.ctx 
				(Boolean.mk_or solver.ctx [
				(Boolean.mk_eq solver.ctx a_solv d_solv);
				(Boolean.mk_eq solver.ctx b_solv c_solv)
				])
			] in
		if (Solver.check solver.solv query)=UNSATISFIABLE
		then rest_sigma, [Exp.BinOp(Peq, a, d); Exp.BinOp(Peq, b, c)] @ rest_pi
		else  Dlseg(a,b,c,d,l,shared) :: rest_sigma, rest_pi

	| first:: rest -> 
		let rest_sigma,rest_pi=(prune_empty_lsegs_ll rest solver) in
		first::rest_sigma, rest_pi


let prune_empty_lsegs form =
	let solver=config_solver_to (Config.solver_timeout_simplify ()) in
	Solver.push solver.solv;
	Solver.add solver.solv (formula_to_solver solver.ctx form);
	let sigma_pruned, added_pi = prune_empty_lsegs_ll form.sigma solver in
	let res={sigma=sigma_pruned;pi=form.pi @ added_pi} in
	Solver.pop solver.solv 1;
	res





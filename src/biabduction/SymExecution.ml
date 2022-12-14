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

open State
open Formula
open Z3
open Z3wrapper

(*** APPLAYING CONTRACTS ***)

type contract_app_res =
  | CAppOk of State.t list
  | CAppFail

(* apply contract,
   * we assume that contract variables are not used within the state s,
   * only the program variables may appear in both contract and state, they are used as anchors
*)
exception Split_contract_RHS

exception NoContract of (string * Config.src_pos)

exception BadRerun

exception NoApplicableRule of (string * CL.Loc.t option)

(*  Checke whether expr should be added to form_z3
     false iff form_z3 => expr (no need to add expr)
     true othervice (incl. timeout)
*)
let prune_expr {ctx=ctx; solv=solv; z3_names=z3_names} form_z3 expr =
	let query= (Boolean.mk_not ctx (expr_to_solver_only_exp ctx z3_names expr)) :: form_z3 in
	not ((Solver.check solv query)=UNSATISFIABLE)

let rec split_pointsto_with_eq_dest rhs dest deltas split_items=
	match rhs with
	| [] -> [],[]
	| Hpointsto (a,l,b)::rest ->
		(if b=dest 
		then 
			let rec create_new_pointsto split_items deltas base=
				match split_items,deltas with
				| [],[] -> [],[]
				| Hpointsto (_,l1,b1):: items_rest,delta::deltas_rest ->
					let npto,nbaseeq=create_new_pointsto items_rest deltas_rest base in
					if delta=Exp.zero 
					then (Hpointsto (a,l1,b1) :: npto), nbaseeq
					else 
						(Hpointsto (Exp.BinOp(Pplus,a,delta),l1,b1) :: npto), 
						(Exp.BinOp(Peq,Exp.UnOp(Base,base),Exp.UnOp(Base,Exp.BinOp(Pplus,a,delta)))) :: nbaseeq
				| _ -> raise Split_contract_RHS
			in
			let new_pointsto,baseeq=create_new_pointsto split_items deltas a in
			let rec_pointsto,rec_baseeq=split_pointsto_with_eq_dest rest dest deltas split_items in
			new_pointsto @ rec_pointsto, baseeq @ rec_baseeq
		
		else 
			let rec_pointsto,rec_baseeq=split_pointsto_with_eq_dest rest dest deltas split_items in
			(Hpointsto (a,l,b) :: rec_pointsto),rec_baseeq
		)
	| first::rest -> 
			let rec_pointsto,rec_baseeq=split_pointsto_with_eq_dest rest dest deltas split_items in
			(first :: rec_pointsto), rec_baseeq

let rec split_contract_rhs rhs rec_splits =
	match rec_splits with
	| [] -> rhs
	| Abduction.NoRecord :: rest ->  split_contract_rhs rhs rest
	| Record (a,b,deltas)::rest ->
		let eq x=(x=a) in
		let neq a = not (eq a) in
		if List.exists eq rhs.sigma 
		then 
			let dest=match a with
				| Hpointsto (_,_,b) -> b
				| _ -> raise Split_contract_RHS
			in
			let new_rhs1=(List.filter neq rhs.sigma) in
			let new_rhs2,added_baseeq=split_pointsto_with_eq_dest new_rhs1 dest deltas b.sigma in
		     split_contract_rhs {sigma=new_rhs2@b.sigma; pi=rhs.pi@b.pi@added_baseeq} rest
		else split_contract_rhs rhs rest


let apply_contract solver fst_run state c pvars =
  match (Abduction.biabduction solver fst_run state.curr c.Contract.lhs pvars) with
  | BFail -> CAppFail
  | Bok  abd_result ->
	let process_abd_result (miss, fr, l_vars,rec_splits) =
	    (* prune useless constrains in miss.pi *)
	    let solver_for_pruning=
	    	let solver2=config_solver_to (Config.solver_timeout_simplify ()) in
		Solver.add solver2.solv (formula_to_solver solver2.ctx state.miss);
		solver2
	    in
	    let new_lvars=(state.lvars @ l_vars) in
	    let pruned_miss_pi=List.filter (prune_expr solver_for_pruning []) miss.pi in
	    let missing= Simplify.prune_empty_lsegs {pi=state.miss.pi @ pruned_miss_pi; sigma=state.miss.sigma @ miss.sigma } in
	    let splited_rhs=split_contract_rhs c.rhs rec_splits in
	    let current= Simplify.prune_empty_lsegs {pi=fr.pi @ splited_rhs.pi; sigma= fr.sigma @ splited_rhs.sigma } in	    
	    {miss=missing; curr=current; lvars=new_lvars; through_loop = state.through_loop}
	in
	let res=List.map process_abd_result abd_result in
    	CAppOk res



(* to avoid conflicts, we rename the contract variables, which appear in state 
   pvars - a list of program variables (global vars + vars used in function) *)
let rec rename_contract_vars_ll state c seed pvars =
  let svars= (find_vars state.curr) @ (find_vars state.miss) in
  let rec seq_list i =
	if (i=0) 
	then []
	else (seq_list (i-1))@[i]
  in
  let cvars = seq_list c.Contract.cvars in
  let conflicts = svars @ cvars @ pvars in
  let mem x l =
    let eq y= (x=y) in
    List.exists eq l
  in
  let rec get_fresh_var s confl =
    if (mem s confl)
    then get_fresh_var (s+1) confl
    else s
  in
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
  | n -> let new_var = get_fresh_var seed conflicts in
         let new_c={ Contract.lhs=substitute_vars_cvars (Var new_var) (CVar n) c.lhs;
           rhs=substitute_vars_cvars (Var new_var) (CVar n) c.rhs;
           cvars=(n-1);
           pvarmap=substitute_varmap new_var n c.pvarmap;
           s=c.s;
         } in
         (rename_contract_vars_ll state new_c (new_var+1) pvars)


(* RENAMING AFTER CONTRACT APPLICATION
   for each tuple (a,b) \in pvarmap
  * rename all occurences of a by a fresh lvar
  * rename all occurences of b by a
*)
let rec post_contract_application_vars state pvarmap seed pvars=
 let conflicts = pvars @ (find_vars state.miss) @ (find_vars state.curr) in
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
      let new_var=get_fresh_var seed conflicts in
      let tmp_curr=substitute_vars new_var a state.curr in
      let new_curr=substitute_vars a b tmp_curr in
      let tmp_miss=substitute_vars new_var a state.miss in
      let new_miss=substitute_vars a b tmp_miss in
      let new_lvars=
        let eq y= not (b=y) in
        List.filter eq state.lvars
      in
      let new_state={ curr=new_curr;
          miss= new_miss;
          lvars=new_lvars @ [new_var];
          through_loop = state.through_loop
        } in
      (post_contract_application_vars new_state rest (new_var+1) pvars)

(* after contract application do the following thing
  1: rename variables according to pvarmap
  2: OBSOLATE, NO MORE APPLIED: for each freed(x) predicate in pure part remove the spatial predicates
     with the equal base
*)
let post_contract_application state solver pvarmap pvars =
  let step1=post_contract_application_vars state pvarmap 1 pvars in
  let vars= CL.Util.list_join_unique (find_vars step1.curr) (find_vars step1.miss) in
  let notmem l x =
      let eq y= (x=y) in
      not (List.exists eq l)
  in
  let new_lvars=List.filter (notmem pvars) vars in
  let final_state={
    miss=step1.miss;
    curr=(* Simplify.remove_freed_and_invalid_parts solver  *)step1.curr;
    lvars=new_lvars;
    through_loop = step1.through_loop} in
  (* check that both parts of the resulting state are satisfiable, if timeout
   apper, we just try it *)
  let sat_query_curr=formula_to_solver solver.ctx final_state.curr in
  let sat_query_missing=formula_to_solver solver.ctx final_state.miss in
  if ((Solver.check solver.solv sat_query_curr)=UNSATISFIABLE) 
  then []
  else
  if ((Solver.check solver.solv sat_query_missing)=UNSATISFIABLE)
  then (
    (*prerr_endline "------------";
    prerr_endline (State.to_string final_state);
    prerr_endline "SAT Fail (Contract application)"; *)
    [] )
  else [final_state]
(* Do
   1) rename conflicting contract variables
   2) apply the contract using biabduction, if not fst_run, skip learn rules
   3) apply post contract renaming
   pvars - a list of global program variables + local program variables (avoid
           name conflicts)
   --- the variables used in state/contract are captured automatically, but
   thery may be some global/local variables, which are not used within state
   and contract
*)
let contract_application solver fst_run state c pvars =
  let c_rename = rename_contract_vars_ll state c 1 pvars in
  let rec get_vars_from_varmoves varmoves =
    match varmoves with
    | [] -> []
    | (a,b)::rest -> [a;b]@get_vars_from_varmoves rest
  in
  (* Some rules in abduction procedure creates fresh variables.
     Therefore all used variables must be provided to abduction call to 
     avoid creation of a logical variable with the same ID within abduction *)
  let used_vars=pvars @ (get_vars_from_varmoves c_rename.pvarmap)
    @ (find_vars state.miss) @ (find_vars state.curr) 
    @ (find_vars c_rename.lhs) @ (find_vars c_rename.rhs) in
  match (apply_contract solver fst_run state c_rename used_vars) with
  | CAppFail -> CAppFail
  | CAppOk s_applied ->  
    (* The post contract application must be called with pvars. All variables
    outside pvars are considered to be logical. *)
    let postprocess st =
      post_contract_application st solver c_rename.pvarmap pvars
    in
    (* If Config.abduction_strategy=1 then s_applied can contain more then
    a single result. *)
    let res = List.concat (List.map postprocess s_applied) in
      match res with
      | [] -> CAppFail
      | _ -> CAppOk res


(* PREPARE STATE FOR CONTRACT
  rename all variables expect parameters and global (fixed_vars) -
  set existential connected with them as fresh contract variables
*)

let rec state2contract ?(status=Contract.OK) cvar s =
  match s.lvars with
  | [] -> {Contract.lhs = s.miss; rhs = s.curr; cvars = cvar; pvarmap = []; s = status}
  | var::tl -> let new_cvar = cvar + 1 in
      let new_s = {
        miss = substitute_vars_cvars (CVar new_cvar) (Var var) s.miss;
        curr = substitute_vars_cvars (CVar new_cvar) (Var var) s.curr;
        lvars = tl;
        through_loop = s.through_loop} in
      state2contract ~status:status new_cvar new_s

 let rec states2contracts states = List.map (state2contract 0) states     

(* substitue gvars used (new_rhs <> c.rhs) in function of contract c and add
   corresponding pvarmoves *)
let rec add_gvars_moves gvars c =
  match gvars with
  | [] -> c
  | gvar::tl -> let new_cvar = c.Contract.cvars + 1 in
    let new_rhs = substitute_vars_cvars (CVar new_cvar) (Var gvar) c.rhs in
    let new_c = if (new_rhs = c.rhs) then c
    else {Contract.lhs = c.lhs; rhs = new_rhs; cvars = new_cvar; pvarmap = (gvar,new_cvar)::c.pvarmap; s = c.s} in
	(add_gvars_moves tl new_c)

(* check for abstract object in precondition and through_loop=true *)
let check_if_rerun tbl s =
  Config.rerun () && tbl.StateTable.fst_run &&
  (s.through_loop=true || is_abstract s.miss) && s.miss!=Formula.empty

(* check if rerun *)
let check_rerun tbl =
  Config.rerun () && (not tbl.StateTable.fst_run)

(* note: error from call of error() *)

let set_fnc_error_contract ?(status=Contract.OK) solver fnc_tbl bb_tbl states insn =
  if check_rerun bb_tbl then raise_notrace BadRerun;
  Config.debug2 ">>> final error contract";
  let fixed = (CL.Util.get_anchors_uid bb_tbl.StateTable.fuid) @ CL.Util.stor.global_vars in
  let get_err_contract s =
    let (removed_sigma,new_miss) = Simplify.formula solver fixed s.miss in
    if (removed_sigma) then
      Config.prerr_error "impossible precondition" insn.CL.Fnc.loc;
    let msg = "error from call of "^(CL.Printer.insn_to_string insn) in
    if (status=Error) then (* already reported error *)
      Config.prerr_note msg insn.loc
    else
      Config.prerr_error msg insn.loc;
    let removed_vars = CL.Util.list_diff (find_vars new_miss) fixed in
    let s_err =
      {miss = new_miss;
      curr = Formula.empty(* {pi = [Exp.Const (Bool false)]; sigma = []} *);
      lvars = removed_vars;
      through_loop = s.through_loop} in

    let c_err = state2contract ~status:Error 0 s_err in
    Config.debug3 (Contract.to_string c_err);
    Some c_err
  in
  let c_errs = List.filter_map get_err_contract states in
  SpecTable.add fnc_tbl bb_tbl.fuid c_errs

(* TODO reimplementation ! *)
let set_fnc_unfinished_contract fnc_tbl fuid =
    Config.debug2 ">>> no contracts";
    SpecTable.only_add fnc_tbl fuid []
(*   Config.debug2 ">>> final unfinished contract";
  let c = Contract.contract_for_unfinished_fnc (CL.Util.get_fnc fuid) in
  Config.debug3 (Contract.to_string c);
  SpecTable.only_add fnc_tbl fuid (c::[]) *)

(* anchors - existential vars representing arguments of function and original
   value of gvars
   gvars - global variables (may appear after calling function)
   tmp_vars - local program variables *)
let set_fnc_contract ?status:(status=Contract.OK) solver fnc_tbl bb_tbl states insn =
  Config.debug2 ">>> final contract";
  let anchors = CL.Util.get_anchors_uid bb_tbl.StateTable.fuid in
  let gvars = CL.Util.stor.global_vars in
  let fvars = CL.Util.get_fnc_vars bb_tbl.fuid in
  let tmp_vars = CL.Util.list_diff fvars gvars in
  if (4 <= Config.verbose ()) then (
    prerr_string "PVARS:";
    CL.Util.print_list ~oc:stderr Exp.variable_to_string fvars;
    prerr_endline "";
    prerr_string "ANCHORS:";
    CL.Util.print_list ~oc:stderr Exp.variable_to_string anchors;
    prerr_endline "";
    prerr_string "GVARS:";
    CL.Util.print_list ~oc:stderr Exp.variable_to_string gvars;
    prerr_endline "";);

  let memcheck_gvars = (
    if (Config.exit_leaks ()) then
      let fname = CL.Printer.get_fnc_name (CL.Util.get_fnc bb_tbl.fuid) in
      match status with
      | OK when fname = Config.main () -> [] (* report memory leaks for static vars *)
      | Aborted -> [] (* report memory leaks for static vars *)
      | _ -> gvars
    else gvars ) in
  let fixed = 0::(anchors @ memcheck_gvars) in
  let loc = insn.CL.Fnc.loc in
  let get_contract s =
      let removed_vars = tmp_vars @ s.lvars in
      let nostack_s = {
        miss = s.miss;
        curr = Simplify.remove_stack ~replaced:true solver s.curr;
        lvars = removed_vars;
        through_loop = s.through_loop} in
      try
        let subs = Simplify.state solver fixed nostack_s loc in
        Config.debug4 (State.to_string subs);
        let need_rerun = check_if_rerun bb_tbl subs in
        if (not(need_rerun) && is_invalid subs.curr.pi) then
          Config.prerr_warn "function returns address of local variable" loc;
        if need_rerun then ( (* add contract which need to be rerun *)
          StateTable.add_rerun bb_tbl subs;
          Config.debug3 ">>> need rerun, candidate:";
          Config.debug3 ("LHS: "^Formula.to_string subs.miss);
          None )
        else if check_rerun bb_tbl then (
          (* add possible final contract after 2nd run *)
          StateTable.add_rerun bb_tbl subs;
          None
        )
        else (
          let c = state2contract ~status:status 0 subs in
          let new_c = add_gvars_moves gvars c in
          Config.debug3 (Contract.to_string new_c);
          Some new_c )
      with
      | Simplify.RemovedSpatialPartFromMiss -> (
        set_fnc_error_contract solver fnc_tbl bb_tbl [nostack_s] insn;
        None
      )
      | Simplify.RemovedSpatialPartFromCurr -> ( (* TODO error: memory leak *)
        set_fnc_error_contract solver fnc_tbl bb_tbl [nostack_s] insn;
        None
      )
  in
  let fnc_c = List.filter_map get_contract states in
  SpecTable.add fnc_tbl bb_tbl.fuid fnc_c


(* NEW STATES *)

(* if contracts not empty, applay each contract on each state for instruction
  [insn] *)
let new_states_for_insn empty_is_err solver tbl bb_tbl insn states c =
  (* Applay each contract on each state *)
  let empty_is_err_ref = ref empty_is_err in
  let rec apply_contracts_on_states states contracts =
    let pvars = CL.Util.get_pvars bb_tbl.StateTable.fuid in
    match states with
    | [] -> []
    | s::tl ->

      let rec solve_contract contracts =
        match contracts with
        | [] -> []
        | c::tl -> Config.debug4 (Contract.to_string c);

          let rec process_new_states abd_states =
            match abd_states with
            | [] -> []
            | a::atl ->
              try
                let simple_a = Simplify.state solver pvars a insn.CL.Fnc.loc in
                Config.debug3 (State.to_string simple_a);
                match c.s with
                | OK | Unfinished -> simple_a::(process_new_states atl)
                | Nondet ->
                  let nondet_s = State.set_through_loop simple_a in
                  nondet_s::(process_new_states atl)
                | Error ->
                  set_fnc_error_contract ~status:c.s solver tbl bb_tbl [simple_a] insn;
                  empty_is_err_ref := false;
                  process_new_states atl
                | Aborted ->
                  set_fnc_contract ~status:c.s solver tbl bb_tbl [simple_a] insn;
                  empty_is_err_ref := false;
                  process_new_states atl

              with
              | Simplify.RemovedSpatialPartFromMiss -> (
                Config.debug3 (State.to_string a);
                set_fnc_error_contract solver tbl bb_tbl [s] insn;
                empty_is_err_ref := false;
                process_new_states atl
              )
              | Simplify.RemovedSpatialPartFromCurr -> (
                Config.debug3 (State.to_string a); (* TODO error: memory leak *)
                set_fnc_error_contract solver tbl bb_tbl [s] insn;
                empty_is_err_ref := false;
                process_new_states atl
              )
          in (* end of process_new_states *)

          let res = contract_application solver bb_tbl.fst_run s c pvars in
          match res with
          | CAppFail -> solve_contract tl (* FIXME error handling *)
          | CAppOk abd_s -> (process_new_states abd_s) @ (solve_contract tl)

      in (* end of solve_contract *)

      (solve_contract contracts) @ (apply_contracts_on_states tl contracts)
  in

  if (c = []) then
    states (* no need applaying empty contracts *)
  else (
    let new_states = apply_contracts_on_states states c in
    if (!empty_is_err_ref && new_states = []) then (
      (* error appears, continue with empty states *)
      set_fnc_error_contract solver tbl bb_tbl states insn;[])
    else new_states
  )


(* FIND CONTRACT FOR CALLING FUNCTION *)

(* @raise NoContract if no contract in tbl for function [fuid] becouse of wrong
   order or recursive function *)
let find_fnc_contract tbl dst args fuid =
  let patterns = SpecTable.find_opt tbl fuid in
  match patterns with
  | None -> raise_notrace (NoContract ("No contract (wrong functions order or recursion)",__POS__))
  | Some p ->
    let rec rename_fnc_contract c =
      match c with
      | [] -> []
      | pattern::tl ->
        let c_rename = Contract.contract_for_called_fnc dst args fuid pattern in
        let c_rest = rename_fnc_contract tl in
        c_rename::c_rest
    in
    rename_fnc_contract p


(*** EXECUTION ***)

let solver = config_solver ()

let rec exec_block tbl bb_tbl states (uid, bb) =
  if (states = [])
  then states
  else (
    Config.debug3 (">>> executing block L"^(string_of_int uid )^":");
    let new_states = (if not (Config.entailment_on_loop_edges_only ())
      then (* entailemt on each basic block entry *)
        StateTable.add ~entailment:true bb_tbl uid states
      else (* no entailment *)
        StateTable.add bb_tbl uid states ) in
    exec_insns tbl bb_tbl new_states bb.CL.Fnc.insns
  )

and exec_insn tbl bb_tbl states insn =
  let get_new_states ?(empty_is_err=true) c =
    new_states_for_insn empty_is_err solver tbl bb_tbl insn states c
  in
  let entailment_if_end_loop bb_uid ss =
    if (Config.entailment_on_loop_edges_only () &&
       CL.Util.is_loop_closing_block bb_uid insn)
      then StateTable.add ~entailment:true bb_tbl bb_uid ss
      else ss
  in
  if (3 <= Config.verbose ()) then CL.Printer.prerr_insn insn;
  match insn.CL.Fnc.code with
  | InsnJMP uid -> let bb = CL.Util.get_block uid in
    let s_jmp = entailment_if_end_loop uid states in
    exec_block tbl bb_tbl s_jmp bb
  | InsnCOND (op,uid_then,uid_else) ->
    let c = Contract.get_contract insn in
    let cond_var = CL.Util.get_var_uid_from_op op in
	let known_vars = CL.Util.get_anchors_uid bb_tbl.StateTable.fuid @ CL.Util.stor.global_vars in

    let set_nondet s =
      if s.through_loop = false && not(var_is_reachable s.miss cond_var known_vars)
      then State.set_through_loop s
      else s
    in

    let get_branch uid c_one =
        let new_s = get_new_states ~empty_is_err:false [c_one] in
        let ss = entailment_if_end_loop uid new_s in
        let sss = if Config.rerun () && bb_tbl.fst_run
          then List.map set_nondet ss
          else ss in
        let bb = CL.Util.get_block uid in
        (sss,bb)
    in
    let (s_then,bb_then) = get_branch uid_then (List.hd c) in
    let (s_else,bb_else) = get_branch uid_else (List.nth c 1) in
    (exec_block tbl bb_tbl s_then bb_then) @ (exec_block tbl bb_tbl s_else bb_else)
  | InsnSWITCH _ -> assert false
  | InsnRET _ ->
    let c = Contract.get_contract insn in
    let new_states = get_new_states c in
    set_fnc_contract solver tbl bb_tbl new_states insn; []
  | InsnABORT ->
    set_fnc_contract ~status:Aborted solver tbl bb_tbl states insn;
    []
  | InsnNOP | InsnLABEL _ -> states
  | InsnCALL ops -> ( match ops with
    | dst::called::args ->
      let no_contracts () =
        let fnc_name = CL.Printer.operand_to_string called in
        raise_notrace (NoApplicableRule (fnc_name,insn.loc))
      in

      if (CL.Util.is_extern called)
      then (
        let c = Contract.get_contract insn in
        get_new_states c
      ) else (
        let c = find_fnc_contract tbl dst args
                                  (CL.Util.get_fnc_uid_from_op called) in
        if c = [] then no_contracts ();
        let s_call = get_new_states ~empty_is_err:false c in
        if s_call = [] then no_contracts ();
        if s_call != [] && Config.abstract_on_call_done ()
        then StateTable.try_abstraction_on_states solver bb_tbl.fuid s_call
        else s_call
      )
    | _ -> assert false )
  | _ -> let c = Contract.get_contract insn in get_new_states c

and exec_insns tbl bb_tbl states insns =
  if (states = [])
  then states
  else (
    match insns with
    | [] -> states
    | insn::tl -> let s = exec_insn tbl bb_tbl states insn in
      exec_insns tbl bb_tbl s tl
  )

(* FIXME: exception for non-pointer static variables *)
let exec_zeroinitializer _(* fuid *) s (uid, var) =
  let assign exp =
    let pi_add = Exp.BinOp (Peq, Var uid, exp) in
    {miss = s.miss;
    curr = {pi=pi_add::s.curr.pi; sigma=s.curr.sigma};
    lvars = s.lvars; through_loop = s.through_loop}
  in
  let typ_code = CL.Util.get_type_code var.CL.Var.typ in
  match typ_code with
  | CL.Type.TypeInt | TypeChar | TypeEnum -> assign Exp.zero
  | TypePtr _ | TypeString -> assign Exp.null
  | TypeBool -> assign (Const (Bool false))
  | TypeReal -> assign (Const (Float 0.0))
  | TypeStruct _ | TypeUnion _ | TypeArray _ ->
    (* l1 -(type.size)-> 0 & static(l1,var) & len(l1)=type.size & base(l1)=l1 *)
    raise_notrace (Contract.ErrorInContract ("static object unsupported",__POS__))
    (* let fresh_var = State.get_fresh_lvar fuid s.lvars in
    let size, stor = Contract.get_storage_with_size (Var fresh_var) (Var uid) in
    let sig_add = Hpointsto ((Var fresh_var), size, Exp.zero) in
    {miss = s.miss;
    curr = {pi=s.curr.pi @ stor; sigma=sig_add::s.curr.sigma};
    lvars = fresh_var::s.lvars} *)
  | TypeFnc _ -> assert false
  | _ -> s

(* add anchors into LHS, if main(int argc, char **argv)
   MISS: arg1=argc & arg2=argv & arg2 -(l1)->Undef & (len(arg2)=l1) &
        (base(arg2)=arg2) & (0<=l1) & (l1=arg1*32)
   CURR: arg1=argc & arg2=argv

   execute initials of all global variables, if they are initialized
   fuid belons to function 'main' *)
(* FIXME no need tbl arguments *)
let init_state_main tbl bb_tbl =
  let rec exec_init_global_var states vars =
    match vars with
    | [] -> states
    | uid::tl -> let gv = CL.Util.get_var uid in
      if (gv.initials=[]) && not(gv.is_extern) then
        match states with (* implicit initialization *)
        | [s] -> (
          let new_s = exec_zeroinitializer bb_tbl.StateTable.fuid s (uid,gv) in
          Config.debug3 (State.to_string new_s);
          exec_init_global_var [new_s] tl )
        | _ -> assert false (* expect exactly 1 init state *)
      else (* explicit initialization *)
        exec_init_global_var (exec_insns tbl bb_tbl states gv.initials) tl
  in
  let init_state = State.init_main bb_tbl.fuid in
  Config.debug2 ">>> initializing global variables";
  (exec_init_global_var (init_state::[]) CL.Util.stor.global_vars)

let exec_fnc fnc_tbl f =
  if (CL.Util.is_extern f.CL.Fnc.def) then () else (
    let fnc_decl_str = CL.Printer.fnc_declaration_to_string f in
    Config.debug1 (">>> executing function "^fnc_decl_str^":");
    let fuid = CL.Util.get_fnc_uid f in
    let bb_tbl = StateTable.create fuid in (* for states on basic block entry *)
    let fname = CL.Printer.get_fnc_name f in
    let init_states =
      if fname = Config.main ()
      then init_state_main fnc_tbl bb_tbl
      else (State.init fuid)::[] in
    let states = (try
      let run1 = exec_block fnc_tbl bb_tbl init_states (List.hd f.cfg) in
      if Config.rerun () && bb_tbl.rerun!=[]
      then (

        let rerun_states = StateTable.start_rerun bb_tbl in
        Config.debug2 (">>> executing reruns for function "^fnc_decl_str^":");
        let pvars = CL.Util.get_pvars fuid in
        (* let nop = CL.Util.get_NOP () in *)

        let apply_init_contract init_c = (* allow learn *)
          let res = contract_application solver true (List.hd init_states)
                    (Contract.rw_rhs init_c) pvars in
          match res with
          | CAppFail -> raise_notrace BadRerun
          | CAppOk abd_s -> abd_s
        in

        let rec rerun_for_contracts rcontracts =
          match rcontracts with
          | [] -> []
          | rc::rtl -> (
            let states2 = (try
              let rstates = apply_init_contract rc in
              let run2 = exec_block fnc_tbl bb_tbl rstates (List.hd f.cfg) in
              (* add contracts after 2nd run *)
              let final_states = StateTable.start_rerun bb_tbl in
              (* let final_contracts = List.map (Contract.rw_lhs rc.lhs) rerun_contracts2 in *)
              SpecTable.add fnc_tbl bb_tbl.fuid (states2contracts final_states);
              run2
            with BadRerun ->
              StateTable.reset_rerun bb_tbl;
              incr Config.statistics.badrerun;
              Config.prerr_note "Discard precondition after 2nd run" (CL.Util.get_fnc_loc f);
              Config.debug3 ("LHS: "^Formula.to_string rc.lhs); []
            ) in
            states2 @ rerun_for_contracts rtl )
        in

        run1 @ rerun_for_contracts (states2contracts rerun_states))

      else run1
    with
      | StateTable.EntailmentLimit loc ->
        Config.prerr_note "Limit reached (increase 'entailment_limit')" loc;
        set_fnc_unfinished_contract fnc_tbl fuid;
        []
      | NoApplicableRule (fnc,loc) ->
        Config.prerr_note ("No applicable contract for function "^fnc^"()") loc;
        set_fnc_unfinished_contract fnc_tbl fuid;
        []
      | CloseLambda.ErrorInLambdaClosing loc ->
        Config.prerr_internal "Lambda closing failed" loc;
        set_fnc_unfinished_contract fnc_tbl fuid;
        []
      | Formula.ErrorInFormula (msg,loc) ->
        Config.prerr_internal (msg^" (formula)") loc;
        set_fnc_unfinished_contract fnc_tbl fuid;
        []
      | Abstraction.ErrorInAbstraction (msg,loc) ->
        Config.prerr_internal (msg^" (abstraction)") loc;
        set_fnc_unfinished_contract fnc_tbl fuid;
        []
      | Contract.ErrorInContract (msg,loc) | NoContract (msg,loc) ->
        Config.prerr_internal msg loc;
        set_fnc_unfinished_contract fnc_tbl fuid;
        []
    ) in
    assert (states = []);
    StateTable.reset bb_tbl;
  )

open State
open Formula
open Z3
open Z3wrapper

(*** APPLAYING CONTRACTS ***)

type contract_app_res =
  | CAppOk of State.t
  | CAppFail

(* apply contract,
   * we assume that contract variables are not used within the state s,
   * only the program variables may appear in both contract and state, they are used as anchors
*)
let prune_expr {ctx=ctx; solv=solv; z3_names=z3_names} form_z3 expr =
	let query= (Boolean.mk_not ctx (expr_to_solver_only_exp ctx z3_names expr)) :: form_z3 in
	(Solver.check solv query)=SATISFIABLE

let apply_contract solver state c pvars =
  match (Abduction.biabduction solver state.curr c.Contract.lhs pvars) with
  | BFail -> CAppFail
  | Bok  (miss, fr, l_vars) ->
    (* prune useless constrains in miss.pi *)
    let pruned_miss_pi=List.filter (prune_expr solver (formula_to_solver solver.ctx state.curr)) miss.pi in
    let missing= {pi=state.miss.pi @ pruned_miss_pi; sigma=state.miss.sigma @ miss.sigma } in
    let current= {pi=fr.pi @ c.rhs.pi; sigma= fr.sigma @ c.rhs.sigma } in
    (* Note that the created contract may be temporarily UNSAT due to the "freed" predicate. 
       The post_contract_application function takes care about it. *)
    CAppOk {miss=missing; curr=current; lvars=(state.lvars @ l_vars)  }



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
         } in
         (rename_contract_vars_ll state new_c (new_var+1) pvars)


exception State_lhs_contains_forbidden_vars

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
        } in
      (post_contract_application_vars new_state rest (new_var+1) pvars)

(* REMOVE THE FREED PARTS *)

exception Conflict_between_freed_and_slseg

let remove_freed_parts {ctx=ctx; solv=solv; z3_names=z3_names} form =
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
        (expr_to_solver_only_exp ctx z3_names base)
        (Expr.mk_app ctx z3_names.base [(expr_to_solver_only_exp ctx z3_names a)])
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
let post_contract_application state solver pvarmap pvars =
  let step1=post_contract_application_vars state pvarmap 1 pvars in
  let vars= CL.Util.list_join_unique (find_vars step1.curr) (find_vars step1.miss) in
  let notmem l x =
      let eq y= (x=y) in
      not (List.exists eq l)
  in
  let new_lvars=List.filter (notmem pvars) vars in
  let final_contract={miss=step1.miss; curr=(remove_freed_parts solver step1.curr); lvars=new_lvars} in
   (* check that both parts of the resulting state are satisfiable *)
  let sat_query_currual=formula_to_solver solver.ctx final_contract.curr in
  let sat_query_missing=formula_to_solver solver.ctx final_contract.miss in
  if ((Solver.check solver.solv sat_query_currual)=SATISFIABLE) &&
     ((Solver.check solver.solv sat_query_missing)=SATISFIABLE)
  then  CAppOk final_contract
  else (prerr_endline "SAT Fail"; CAppFail)

(* Do
   1) rename conflicting contract variables
   2) apply the contract using biabduction
   3) apply post contract renaming
   pvars - a list of global program variables + local program variables (avoid
           name conflicts)
   --- the variables used in state/contract are captured automatically, but
   thery may be some global/local variables, which are not used within state
   and contract
*)
let contract_application solver state c pvars =
  let c_rename = rename_contract_vars_ll state c 1 pvars in
  match (apply_contract solver state c_rename pvars) with
  | CAppFail -> CAppFail
  | CAppOk s_applied -> (post_contract_application s_applied solver c_rename.pvarmap pvars)

(* Applay each contract on each state *)
let rec apply_contracts_on_states solver fuid states contracts =
  let pvars = CL.Util.get_pvars fuid in
  match states with
  | [] -> []
  | s::tl ->
    let rec solve_contract contracts =
      match contracts with
      | [] -> []
      | c::tl -> Contract.print c;
          let res = contract_application solver s c pvars in
          match res with
          | CAppFail -> solve_contract tl (* FIXME error handling *)
          | CAppOk s ->
            try
              let simple_s = State.simplify2 pvars s in
              State.print simple_s;
              simple_s::(solve_contract tl)
            with State.RemovedSpatialPartFromMiss -> (
              State.print s;
              prerr_endline "!!! error: impossible precondition";
              solve_contract tl
            )
    in
    (solve_contract contracts) @ (apply_contracts_on_states solver fuid tl contracts)

(* Try abstraction on each miss anad act of each state,
   for now only list abstraction *)
let try_abstraction_on_states solver fuid states =
  let pvars = CL.Util.get_pvars fuid in
  let rec try_abstraction states =
    match states with
    | [] -> []
    | s::tl ->
      let new_miss = Abstraction.lseg_abstaction solver s.miss pvars in
      let new_curr = Abstraction.lseg_abstaction solver s.curr pvars in
      let abstract_state = {miss = new_miss; curr = new_curr; lvars=s.lvars} in
      (* TODO: update lvars *)
      abstract_state :: (try_abstraction tl)
  in
  print_endline ">>> trying list abstraction";
  try_abstraction states


(* FIND CONTRACT FOR CALLING FUNCTION *)

let find_fnc_contract tbl dst args fuid curr_fuid =
  let patterns = SpecTable.find_opt tbl fuid in
  match patterns with
  | None -> assert false (* wrong order; recursive function not supported *)
  | Some p ->
    let rec rename_fnc_contract c =
      match c with
      | [] -> []
      | pattern::tl ->
        let c_rename = Contract.contract_for_called_fnc dst args curr_fuid fuid pattern in
        let c_rest = rename_fnc_contract tl in
        c_rename::c_rest
    in
    rename_fnc_contract p


(* PREPARE STATE FOR CONTRACT
  rename all variables expect parameters and global (fixed_vars) -
  set existential connected with them as fresh contract variables
*)

let rec state2contract s cvar =
  match s.lvars with
  | [] -> {Contract.lhs = s.miss; rhs = s.curr; cvars = cvar; pvarmap = []}
  | var::tl -> let new_cvar = cvar + 1 in
      let new_s = {
        miss = substitute_vars_cvars (CVar new_cvar) (Var var) s.miss;
        curr = substitute_vars_cvars (CVar new_cvar) (Var var) s.curr;
        lvars = tl} in
      state2contract new_s new_cvar

(* substitue gvars used in function of contract c and add corresponding
   pvarmoves *)
let rec add_gvars_moves gvars c =
  match gvars with
  | [] -> c
  | gvar::tl -> let new_cvar = c.Contract.cvars + 1 in
    let new_rhs = substitute_vars_cvars (CVar new_cvar) (Var gvar) c.rhs in
    let new_c = {Contract.lhs = c.lhs; rhs = new_rhs; cvars = new_cvar; pvarmap = (gvar,new_cvar)::c.pvarmap} in
	(add_gvars_moves tl new_c)

(* TODO errors handling *)
let set_fnc_error_contract fnc_tbl states _(*code*) fuid =
  print_endline ">>> final error contract";
  let fixed = (CL.Util.get_anchors_uid fuid) @ CL.Util.stor.global_vars in
  let get_err_contract s =
    let (removed_sigma,new_miss) = Formula.simplify2 fixed s.miss in
    if (removed_sigma) then
      prerr_endline "!!! error: impossible precondition";
    let removed_vars = CL.Util.list_diff (find_vars new_miss) fixed in
    let s_err =
      {miss = new_miss;
        curr = {pi = [Exp.Const (Bool false)]; sigma = []};
        lvars = removed_vars} in
    let c_err = state2contract s_err 0 in
    Contract.print c_err;
    c_err
  in
  let c_errs = List.map get_err_contract states in
  SpecTable.add fnc_tbl fuid c_errs

(* anchors - existential vars representing arguments of function and original
   value of used_gvars
   used_gvars - global variables used in function
   tmp_vars - local program variables *)
let set_fnc_contract fnc_tbl states fuid =
  print_endline ">>> final contract";
  let anchors = CL.Util.get_anchors_uid fuid in
  let gvars = CL.Util.stor.global_vars in
  let fvars = CL.Util.get_fnc_vars fuid in
  let used_gvars = CL.Util.list_inter fvars gvars in
  let tmp_vars = CL.Util.list_diff fvars gvars in
  print_string "PVARS:";
  CL.Util.print_list Exp.variable_to_string fvars; print_newline ();
  print_string "ANCHORS:";
  CL.Util.print_list Exp.variable_to_string anchors; print_newline ();
  print_string "GVARS:";
  CL.Util.print_list Exp.variable_to_string used_gvars; print_newline ();

  let fixed = 0::(anchors @ used_gvars) in
  let get_contract s =
      try
        let removed_vars = tmp_vars @ s.lvars in
        let tmp_s = {miss = s.miss; curr = s.curr; lvars = removed_vars} in
        let subs = State.simplify2 fixed tmp_s in
        State.print subs;
        let c = state2contract subs 0 in
        let new_c = add_gvars_moves used_gvars c in
        Contract.print new_c;
        Some new_c
      with State.RemovedSpatialPartFromMiss -> (
        set_fnc_error_contract fnc_tbl [s] CL.Fnc.InsnNOP fuid;
        None
      )
  in
  let fnc_c = List.filter_map get_contract states in
  SpecTable.add fnc_tbl fuid fnc_c


(*** EXECUTION ***)

let solver = config_solver ()

let rec exec_block tbl bb_tbl states (uid, bb) fuid =
  if (states = [])
  then states
  else (
    Printf.printf ">>> executing block L%i:\n%!" uid;
    let new_states = StateTable.add bb_tbl uid states in
    exec_insns tbl bb_tbl new_states bb.CL.Fnc.insns fuid
  )

and exec_insn tbl bb_tbl states insn fuid =
  let new_states_for_insn c =
    if (c = []) then
      states (* no need applaying empty contracts *)
    else (
      let new_states = apply_contracts_on_states solver fuid states c in
        if (new_states = []) then (
          (* error appears, continue with empty states *)
          set_fnc_error_contract tbl states insn.CL.Fnc.code fuid;[])
        else new_states )
  in
  let abstract_if_end_loop bb_uid ss =
    if (CL.Util.is_loop_closing_block bb_uid insn)
      then try_abstraction_on_states solver fuid ss
      else ss
  in
  CL.Printer.print_insn insn;
  match insn.CL.Fnc.code with
  | InsnJMP uid -> let bb = CL.Util.get_block uid in
    let s_jmp = abstract_if_end_loop uid states in
    exec_block tbl bb_tbl s_jmp bb fuid
  | InsnCOND (_,uid_then,uid_else) ->
    let c = Contract.get_contract insn in
    let s_then = apply_contracts_on_states solver fuid states
                 [(List.hd c)] in
    let s_else = apply_contracts_on_states solver fuid states
                 [(List.nth c 1)] in
    let ss_then = abstract_if_end_loop uid_then s_then in
    let ss_else = abstract_if_end_loop uid_else s_else in
    let bb_then = CL.Util.get_block uid_then in
    let bb_else = CL.Util.get_block uid_else in
    (exec_block tbl bb_tbl ss_then bb_then fuid) @ (exec_block tbl bb_tbl ss_else bb_else fuid)
  | InsnSWITCH _ -> assert false
  | InsnNOP | InsnLABEL _ -> states
  | InsnCALL ops -> ( match ops with
    | dst::called::args ->
      let c = ( if (CL.Util.is_extern called)
        then Contract.get_contract insn
        else find_fnc_contract tbl dst args
                               (CL.Util.get_fnc_uid_from_op called) fuid) in
      new_states_for_insn c
    | _ -> assert false )
  | InsnCLOBBER _ -> states (* TODO: stack allocation *)
  | _ -> let c = Contract.get_contract insn in new_states_for_insn c

and exec_insns tbl bb_tbl states insns fuid =
  if (states = [])
  then states
  else (
    match insns with
    | [] -> states
    | insn::tl -> let s = exec_insn tbl bb_tbl states insn fuid in
      exec_insns tbl bb_tbl s tl fuid
  )

let get_zeroinitializer typ_code =
  match typ_code with
  | CL.Type.TypeInt | TypeChar | TypeEnum -> Some Exp.zero
  | TypePtr _ | TypeString -> Some Exp.null
  | TypeBool -> Some (Const (Bool false))
  | TypeReal -> Some (Const (Float 0.0))
  | TypeStruct _ | TypeUnion _ | TypeArray _ -> assert false (* FIXME *)
  | TypeFnc _ -> assert false
  | _ -> None

(* add anchors into LHS, if main(int argc, char **argv)
   MISS: arg1=argc & arg2=argv & arg2 -(l1)->Undef & (len(arg2)=l1) &
        (base(arg2)=arg2) & (0<=l1) & (l1=arg1*32)
   CURR: arg1=argc & arg2=argv

   execute initials of all global variables, if they are initialized
   fuid belons to function 'main' *)
(* FIXME no need tbl and bb_tbl arguments *)
let init_state_main tbl bb_tbl fuid =
  let rec exec_init_global_var states vars =
    match vars with
    | [] -> states
    | uid::tl -> let gv = CL.Util.get_var uid in
      if (gv.initials=[]) && not(gv.is_extern) then
        match states with (* implicit initialization *)
        | [s] -> (
          let zero_exp = get_zeroinitializer (CL.Util.get_type_code gv.typ) in
          match zero_exp with
          | None -> states
          | Some exp ->
            let assign = Exp.BinOp (Peq, Var uid, exp) in
            let new_s = {
              miss = s.miss;
              curr = {pi=assign::s.curr.pi; sigma=s.curr.sigma};
              lvars = s.lvars} in
            exec_init_global_var [new_s] tl )
        | _ -> assert false
      else (* explicit initialization *)
        exec_init_global_var (exec_insns tbl bb_tbl states gv.initials fuid) tl
  in
  let init_state = State.init_main fuid in
  print_endline ">>> initializing global variables";
  (exec_init_global_var (init_state::[]) CL.Util.stor.global_vars)

let exec_fnc fnc_tbl f =
  if (CL.Util.is_extern f.CL.Fnc.def) then () else (
    let fnc_decl_str = CL.Printer.fnc_declaration_to_string f in
    print_endline (">>> executing function "^fnc_decl_str^":");
    let bb_tbl = StateTable.create in (* for states on basic block entry *)
    let fuid = CL.Util.get_fnc_uid f in
    let fname = CL.Printer.get_fnc_name f in
    let init_states =
      if fname = "main"
      then init_state_main fnc_tbl bb_tbl fuid
      else (State.init fuid)::[] in
    let states = exec_block fnc_tbl bb_tbl init_states (List.hd f.cfg) fuid in
    set_fnc_contract fnc_tbl states fuid;
    StateTable.reset bb_tbl;
  )

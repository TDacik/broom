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

exception NoContract of string

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


let apply_contract solver state c pvars =
  match (Abduction.biabduction solver state.curr c.Contract.lhs pvars) with
  | BFail -> CAppFail
  | Bok  abd_result ->
	let process_abd_result (miss, fr, l_vars,rec_splits) =
	    (* prune useless constrains in miss.pi *)
	    let solver_for_pruning=
	    	let solver2=config_solver_to Config.solver_timeout_simplify in
		Solver.add solver2.solv (formula_to_solver solver2.ctx state.miss);
		solver2
	    in
	    let pruned_miss_pi=List.filter (prune_expr solver_for_pruning []) miss.pi in
	    let missing= {pi=state.miss.pi @ pruned_miss_pi; sigma=state.miss.sigma @ miss.sigma } in
	    let splited_rhs=split_contract_rhs c.rhs rec_splits in
	    let current= {pi=fr.pi @ splited_rhs.pi; sigma= fr.sigma @ splited_rhs.sigma } in	    
	    {miss=missing; curr=current; lvars=(state.lvars @ l_vars); through_loop = state.through_loop}
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
  (* check that both parts of the resulting state are satisfiable *)
  let sat_query_curr=formula_to_solver solver.ctx final_state.curr in
  let sat_query_missing=formula_to_solver solver.ctx final_state.miss in
  if ((Solver.check solver.solv sat_query_curr)=SATISFIABLE) &&
     ((Solver.check solver.solv sat_query_missing)=SATISFIABLE)
  then [final_state]
  else (
    (*prerr_endline "------------";
    prerr_endline (State.to_string final_state);
    prerr_endline "SAT Fail (Contract application)";*) 
    [])

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
  let rec get_vars_from_varmoves varmoves =
  	match varmoves with
	| [] -> []
	| (a,b)::rest -> [a;b]@get_vars_from_varmoves rest
  in
  (* Some rules in abduction procedure creates fresh variables.
     Therefore all used variables must be provided to abduction call to 
     avoid creation of a logical variable with the same ID within abduction *)
  let used_vars=pvars @ (get_vars_from_varmoves c_rename.pvarmap)
  	@(find_vars state.miss) @ (find_vars state.curr) 
	@(find_vars c_rename.lhs)@(find_vars c_rename.rhs)in
  match (apply_contract solver state c_rename used_vars) with
  | CAppFail -> CAppFail
  | CAppOk s_applied ->  
  		(* The post contrat application must be called with pvars. All variables outside pvars are considered to be logical. *)
  		let postprocess st = post_contract_application st solver c_rename.pvarmap pvars in
		(* If Config.abduction_strategy=1 then s_applied can contain more then a single result. *)
		let res=List.concat (List.map postprocess s_applied) in
		match res with
		| [] -> CAppFail
		| _ -> CAppOk res


(* PREPARE STATE FOR CONTRACT
  rename all variables expect parameters and global (fixed_vars) -
  set existential connected with them as fresh contract variables
*)

let rec state2contract ?(status=Contract.OK) s cvar =
  match s.lvars with
  | [] -> {Contract.lhs = s.miss; rhs = s.curr; cvars = cvar; pvarmap = []; s = status}
  | var::tl -> let new_cvar = cvar + 1 in
      let new_s = {
        miss = substitute_vars_cvars (CVar new_cvar) (Var var) s.miss;
        curr = substitute_vars_cvars (CVar new_cvar) (Var var) s.curr;
        lvars = tl;
        through_loop = s.through_loop} in
      state2contract ~status:status new_s new_cvar

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
(* FIXME more lvars than used *)
let check_rerun tbl s =
  if Config.rerun () && tbl.StateTable.fst_run &&
    (s.through_loop=true || is_abstract s.miss) && s.miss!=Formula.empty
  then (
    let re_s = {miss = s.miss; curr = Formula.empty; lvars = s.lvars; through_loop = false} in
    StateTable.add_rerun tbl re_s;
    None )
  else Some s


(* note: error from call of error() *)

let set_fnc_error_contract ?(status=Contract.OK) solver fnc_tbl bb_tbl states insn =
  print_endline ">>> final error contract";
  let fixed = (CL.Util.get_anchors_uid bb_tbl.StateTable.fuid) @ CL.Util.stor.global_vars in
  let get_err_contract s =
    let (removed_sigma,new_miss) = Simplify.formula solver fixed s.miss in
    if (removed_sigma) then
      Config.prerr_error "impossible precondition";
    let msg = "error from call of "^(CL.Printer.insn_to_string insn) in
    if (status=Error) then (* already reported error *)
      Config.prerr_note msg
    else
      Config.prerr_error msg;
    let removed_vars = CL.Util.list_diff (find_vars new_miss) fixed in
    let s_err =
      {miss = new_miss;
      curr = Formula.empty(* {pi = [Exp.Const (Bool false)]; sigma = []} *);
      lvars = removed_vars;
      through_loop = s.through_loop} in

    let check = if not removed_sigma then check_rerun bb_tbl s_err else Some s_err in
    match (check) with
    | None -> None
    | Some check_s ->
      let c_err = state2contract ~status:Error check_s 0 in
      Contract.print c_err;
      Some c_err
  in
  let c_errs = List.filter_map get_err_contract states in
  SpecTable.add fnc_tbl bb_tbl.fuid c_errs

let set_fnc_unfinished_contract fnc_tbl fuid =
  print_endline ">>> final unfinished contract";
  let c = Contract.contract_for_unfinished_fnc (CL.Util.get_fnc fuid) in
  Contract.print c;
  SpecTable.only_add fnc_tbl fuid (c::[])

(* anchors - existential vars representing arguments of function and original
   value of gvars
   gvars - global variables (may appear after calling function)
   tmp_vars - local program variables *)
let set_fnc_contract ?status:(status=Contract.OK) solver fnc_tbl bb_tbl states insn =
  print_endline ">>> final contract";
  let anchors = CL.Util.get_anchors_uid bb_tbl.StateTable.fuid in
  let gvars = CL.Util.stor.global_vars in
  let fvars = CL.Util.get_fnc_vars bb_tbl.fuid in
  let tmp_vars = CL.Util.list_diff fvars gvars in
  print_string "PVARS:";
  CL.Util.print_list Exp.variable_to_string fvars; print_newline ();
  print_string "ANCHORS:";
  CL.Util.print_list Exp.variable_to_string anchors; print_newline ();
  print_string "GVARS:";
  CL.Util.print_list Exp.variable_to_string gvars; print_newline ();

  let memcheck_gvars = (
    if (Config.exit_leaks ()) then
      let fname = CL.Printer.get_fnc_name (CL.Util.get_fnc bb_tbl.fuid) in
      match status with
      | OK when fname = Config.main () -> [] (* report memory leaks for static vars *)
      | Aborted -> [] (* report memory leaks for static vars *)
      | _ -> gvars
    else gvars ) in
  let fixed = 0::(anchors @ memcheck_gvars) in
  let get_contract s =
      let removed_vars = tmp_vars @ s.lvars in
      let nostack_s = {
        miss = s.miss;
        curr = Simplify.remove_stack ~replaced:true solver s.curr;
        lvars = removed_vars;
        through_loop = s.through_loop} in
      match (check_rerun bb_tbl nostack_s) with
      | None -> None
      | Some check_s ->
        try
          let subs = Simplify.state solver fixed check_s in
          State.print subs;
          if (is_invalid subs.curr.pi) then
            Config.prerr_warn "function returns address of local variable";
          let c = state2contract ~status:status subs 0 in
          let new_c = add_gvars_moves gvars c in
          Contract.print new_c;
          Some new_c
        with Simplify.RemovedSpatialPartFromMiss -> (
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
        | c::tl -> Contract.print c;

          let rec process_new_states abd_states =
            match abd_states with
            | [] -> []
            | a::atl ->
              try
                let simple_a = Simplify.state solver pvars a in
                State.print simple_a;
                match c.s with
                | OK | Unfinished -> simple_a::(process_new_states atl)
                | Error ->
                  set_fnc_error_contract ~status:c.s solver tbl bb_tbl [simple_a] insn;
                  empty_is_err_ref := false;
                  process_new_states atl
                | Aborted ->
                  set_fnc_contract ~status:c.s solver tbl bb_tbl [simple_a] insn;
                  empty_is_err_ref := false;
                  process_new_states atl

              with Simplify.RemovedSpatialPartFromMiss -> (
                State.print a;
                set_fnc_error_contract solver tbl bb_tbl [s] insn;
                process_new_states atl
              )
          in (* end of process_new_states *)

          let res = contract_application solver s c pvars in
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


(* Try abstraction on each miss anad act of each state,
   for now only list abstraction *)
let try_abstraction_on_states solver fuid states =
  let pvars = CL.Util.get_pvars fuid in
  let rec try_abstraction states =
    match states with
    | [] -> []
    | s::tl ->
      let new_miss = Abstraction.lseg_abstraction solver s.miss pvars in
      let new_curr = Abstraction.lseg_abstraction solver s.curr pvars in
      let abstract_state = {miss = new_miss; curr = new_curr; lvars=s.lvars; through_loop = s.through_loop} in
      (* TODO: update lvars *)
      abstract_state :: (try_abstraction tl)
  in
  print_endline ">>> trying list abstraction";
  try_abstraction states


(* FIND CONTRACT FOR CALLING FUNCTION *)

(* @raise NoContract if no contract in tbl for function [fuid] becouse of wrong
   order or recursive function *)
let find_fnc_contract tbl dst args fuid =
  let patterns = SpecTable.find_opt tbl fuid in
  match patterns with
  | None -> raise_notrace (NoContract "No contract (wrong functions order or recursion)")
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
    Printf.printf ">>> executing block L%i:\n%!" uid;
    let new_states = StateTable.add bb_tbl uid states in
    exec_insns tbl bb_tbl new_states bb.CL.Fnc.insns
  )

and exec_insn tbl bb_tbl states insn =
  let get_new_states ?(empty_is_err=true) c =
    new_states_for_insn empty_is_err solver tbl bb_tbl insn states c
  in
  let abstract_if_end_loop bb_uid ss =
    if (CL.Util.is_loop_closing_block bb_uid insn)
      then try_abstraction_on_states solver bb_tbl.fuid ss
      else ss
  in
  CL.Printer.print_insn insn;
  match insn.CL.Fnc.code with
  | InsnJMP uid -> let bb = CL.Util.get_block uid in
    let s_jmp = abstract_if_end_loop uid states in
    exec_block tbl bb_tbl s_jmp bb
  | InsnCOND (_,uid_then,uid_else) ->
    let c = Contract.get_contract insn in
    let s_then = get_new_states ~empty_is_err:false [(List.hd c)] in
    let s_else = get_new_states ~empty_is_err:false [(List.nth c 1)] in
    let ss_then = abstract_if_end_loop uid_then s_then in
    let ss_else = abstract_if_end_loop uid_else s_else in
    let bb_then = CL.Util.get_block uid_then in
    let bb_else = CL.Util.get_block uid_else in
    (exec_block tbl bb_tbl ss_then bb_then) @ (exec_block tbl bb_tbl ss_else bb_else)
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
      let c = ( if (CL.Util.is_extern called)
        then Contract.get_contract insn
        else find_fnc_contract tbl dst args
                               (CL.Util.get_fnc_uid_from_op called) ) in
      get_new_states c
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
    raise_notrace (Contract.ErrorInContract "static object unsupported")
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
          State.print new_s;
          exec_init_global_var [new_s] tl )
        | _ -> assert false (* expect exactly 1 init state *)
      else (* explicit initialization *)
        exec_init_global_var (exec_insns tbl bb_tbl states gv.initials) tl
  in
  let init_state = State.init_main bb_tbl.fuid in
  print_endline ">>> initializing global variables";
  (exec_init_global_var (init_state::[]) CL.Util.stor.global_vars)

let exec_fnc fnc_tbl f =
  if (CL.Util.is_extern f.CL.Fnc.def) then () else (
    let fnc_decl_str = CL.Printer.fnc_declaration_to_string f in
    print_endline (">>> executing function "^fnc_decl_str^":");
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
        let init_s = (List.hd init_states) in
        let add_curr s =
          (* if init_miss=s.miss
            then None else *)
            (* Some *) {miss = s.miss; curr = init_s.curr; lvars = CL.Util.list_diff s.lvars (CL.Util.get_fnc_args fuid); through_loop = false}
        in

        let rerun_states = List.map add_curr bb_tbl.rerun in
        StateTable.reset bb_tbl; bb_tbl.fst_run <- false;
        print_endline (">>> executing reruns for function "^fnc_decl_str^":");
        CL.Util.print_list_endline State.to_string rerun_states;
        run1 @ exec_block fnc_tbl bb_tbl rerun_states (List.hd f.cfg) )
      else run1
    with
      | StateTable.EntailmentLimit ->
        Config.prerr_internal "Limit reached (increase 'entailment_limit')";
        set_fnc_unfinished_contract fnc_tbl fuid;
        []
      | Abduction.NoApplicableRule ->
        Config.prerr_internal "No applicable abduction rule";
        set_fnc_unfinished_contract fnc_tbl fuid;
        []
      | Abstraction.ErrorInAbstraction msg ->
        Config.prerr_internal (msg^" (abstraction)");
        set_fnc_unfinished_contract fnc_tbl fuid;
        []
      | Contract.ErrorInContract msg | NoContract msg ->
        Config.prerr_internal msg;
        set_fnc_unfinished_contract fnc_tbl fuid;
        []
    ) in
    assert (states = []);
    StateTable.reset bb_tbl;
  )

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
let apply_contract ctx solv z3_names state c pvars =
  match (Abduction.biabduction ctx solv z3_names state.act c.Contract.lhs pvars) with
  | BFail -> CAppFail
  | Bok  (miss, fr, l_vars) ->
    let missing= {pi=state.miss.pi @ miss.pi; sigma=state.miss.sigma @ miss.sigma } in
    let actual= {pi=fr.pi @ c.rhs.pi; sigma= fr.sigma @ c.rhs.sigma } in

    CAppOk {miss=missing; act=actual; lvars=(state.lvars @ l_vars)  }

(* to avoid conflicts, we rename the contract variables, which appear in state 
   pvars - a list of program variables (global vars + vars used in function) *)
let rec rename_contract_vars_ll state c seed pvars =
  let svars= (find_vars state.act) @ (find_vars state.miss) in
  let rec cvars_pvarmap pvarmap =
  	match pvarmap with
	| [] -> []
	| (a,_)::rest -> join_list_unique [a] (cvars_pvarmap rest)
  in
  let cvars= (find_vars c.Contract.lhs) @ (find_vars c.rhs) @ (cvars_pvarmap c.pvarmap) in
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
 let conflicts = pvars @ (find_vars state.miss) @ (find_vars state.act) in
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
      let new_var=get_fresh_var seed conflicts in
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
      (post_contract_application_vars new_state rest (new_var+1) pvars)

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
let post_contract_application state ctx solv z3_names pvarmap pvars =
  let step1=post_contract_application_vars state pvarmap 1 pvars in
  let vars= Formula.join_list_unique (find_vars step1.act) (find_vars step1.miss) in
  let notmem l x =
      let eq y= (x=y) in
      not (List.exists eq l)
  in
  let new_lvars=List.filter (notmem pvars) vars in
  {miss=step1.miss; act=(remove_freed_parts ctx solv z3_names step1.act); lvars=new_lvars}

(* FIND CONTRACT FOR CALLING FUNCTION *)

let find_fnc_contract tbl dst args fuid =
  let patterns = SpecTable.find_opt tbl fuid in
  match patterns with
  | None -> assert false (* wrong order; recursive function not supported *)
  | Some p -> let vars = CL.Util.get_fnc_args fuid in
    let rec rename_fnc_contract c =
      match c with
      | [] -> []
      | pattern::tl ->
        let c_rename = Contract.contract_for_called_fnc dst args vars pattern in
        let c_rest = rename_fnc_contract tl in
        c_rename::c_rest
    in
    rename_fnc_contract p

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
let contract_application ctx solv z3_names state c pvars =
  let c_rename = rename_contract_vars_ll state c 1 pvars in
  match (apply_contract ctx solv z3_names state c_rename pvars) with
  | CAppFail -> CAppFail
  | CAppOk s_applied ->
    CAppOk (post_contract_application s_applied ctx solv z3_names c_rename.pvarmap pvars)

(* PREPARE STATE FOR CONTRACT
  rename all variables expect parameters and global (fixed_vars) -
  set existential connected with them as fresh contract variables
*)

let rec state2contract s vars cvar =
  match vars with
  | [] -> {Contract.lhs = s.miss; rhs = s.act; cvars = cvar; pvarmap = []}
  | var::tl -> let new_cvar = cvar + 1 in
      let new_s = {
        miss = substitute_vars_cvars (CVar new_cvar) (Var var) s.miss;
        act = substitute_vars_cvars (CVar new_cvar) (Var var) s.act;
        lvars = []} in
      state2contract new_s tl new_cvar

let rec get_fnc_contract fixed_vars states =
  match states with
  | [] -> []
  | s::tl -> State.print s; (state2contract s (fixed_vars @ s.lvars) 0) :: (get_fnc_contract fixed_vars tl)

(*** EXECUTION ***)

(* TODO: ctx solv z3_names -> merge into one parameter *)

let cfg = [("model", "true"); ("proof", "false")]
let ctx = (Z3.mk_context cfg)
let solv = (Z3.Solver.mk_solver ctx None)
let z3_names=get_sl_functions_z3 ctx

(* Applay each contract on each state *)
let rec apply_on_state ctx solv z3_names fuid states contracts =
  match states with
  | [] -> []
  | s::tl -> (solve_contract ctx solv z3_names fuid s contracts) @ (apply_on_state ctx solv z3_names fuid tl contracts)

and solve_contract ctx solv z3_names fuid state contracts =
  match contracts with
  | [] -> []
  | c::tl -> Contract.print c;
      let res = contract_application ctx solv z3_names state c
        ((CL.Util.get_fnc_vars fuid) @ CL.Util.stor.global_vars) in
      match res with
      | CAppFail -> [] (* FIXME error handling *)
      | CAppOk s -> State.print s;
        (State.simplify s)::(solve_contract ctx solv z3_names fuid state tl)


let rec exec_block tbl states (uid, bb) fuid =
  Printf.printf ">>> executing block L%i:\n" uid;
  exec_insns tbl states bb.CL.Fnc.insns fuid

and exec_insn tbl states insn fuid =
  match insn.CL.Fnc.code with
  | InsnJMP uid -> let bb = CL.Util.get_block uid in
    exec_block tbl states bb fuid
  | InsnCOND (_,uid_then,uid_else) ->
    CL.Printer.print_insn insn;
    let c = Contract.get_contract insn in
    let s_then = apply_on_state ctx solv z3_names fuid states [(List.hd c)] in
    let s_else = apply_on_state ctx solv z3_names fuid states [(List.nth c 1)] in
    let bb_then = CL.Util.get_block uid_then in
    let bb_else = CL.Util.get_block uid_else in
    (exec_block tbl s_then bb_then fuid) @ (exec_block tbl s_else bb_else fuid)
  | InsnSWITCH _ -> assert false
  | InsnNOP | InsnLABEL _ -> states
  | InsnCALL ops -> ( match ops with
    | dst::called::args ->
      let c = ( if (CL.Util.is_extern called)
        then Contract.get_contract insn
        else find_fnc_contract tbl dst args
		                       (CL.Util.get_fnc_uid_from_op called) ) in
      CL.Printer.print_insn insn;
      if (c = [])
        then states (* no need applaying empty contracts *)
        else apply_on_state ctx solv z3_names fuid states c
    | _ -> assert false )
  | InsnCLOBBER _ -> states (* TODO: stack allocation *)
  | _ -> let c = Contract.get_contract insn in
    CL.Printer.print_insn insn;
    if (c = [])
      then states (* no need applaying empty contracts *)
      else apply_on_state ctx solv z3_names fuid states c

and exec_insns tbl states insns fuid =
  match insns with
  | [] -> states
  | insn::tl -> let s = exec_insn tbl states insn fuid in
    exec_insns tbl s tl fuid


(* execute initials of all global variables, if they are initialized
   fuid belons to function 'main' *)
(* FIXME no need tbl argument *)
let exec_init_global_vars tbl fuid =
  Printf.printf ">>> initializing global variables\n";
  let rec init_global_var states vars =
    match vars with
    | [] -> states
    | uid::tl -> let gv = CL.Util.get_var uid in
      init_global_var (exec_insns tbl states gv.initials fuid) tl
  in
  init_global_var (State.empty::[]) CL.Util.stor.global_vars


(* TODO: state not empty for functions with parameters? *)
let exec_fnc fnc_tbl f =
  if (CL.Util.is_extern f.CL.Fnc.def) then () else (
    Printf.printf ">>> executing function ";
    CL.Printer.print_fnc_declaration f;
    Printf.printf ":\n";
    let fuid = CL.Util.get_fnc_uid f in
    let fname = CL.Printer.get_fnc_name f in
    let init_states = (
      if fname = "main"
      then exec_init_global_vars fnc_tbl fuid
      else State.empty::[]) in
    let states = exec_block fnc_tbl init_states (List.hd f.cfg) fuid in
    Printf.printf ">>> final contract\n";
    print_string "PVARS:";
    CL.Util.print_list Exp.variable_to_string f.vars; print_string "\n";
    print_string "ARGS:";
    CL.Util.print_list Exp.variable_to_string f.args; print_string "\n";
    print_string "GVARS:";
    CL.Util.print_list Exp.variable_to_string CL.Util.stor.global_vars; print_string "\n";
    let fixed_vars =
      CL.Util.list_diff f.vars (f.args @ CL.Util.stor.global_vars) in
    let fnc_c = get_fnc_contract fixed_vars states in
    SpecTable.add fnc_tbl fuid fnc_c;
    CL.Util.print_list Contract.to_string fnc_c
  )

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

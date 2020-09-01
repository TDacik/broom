module FExp = Formula.Exp

type variable = Formula.Exp.variable

type t = { 
    miss: Formula.t;
    act: Formula.t;
    lvars: variable list;
}

(** Raise in case of ... *)
exception RemovedSpatialPartFromMiss

let empty = {miss = Formula.empty; act = Formula.empty; lvars = []}

let to_string state =
  "EXISTS: " ^ Formula.lvariables_to_string state.lvars
  ^ "\nMISS: " ^ Formula.to_string ~lvars:state.lvars state.miss
  ^ "\nACTUAL: " ^ Formula.to_string ~lvars:state.lvars state.act
  
let print state =
  print_endline (to_string state)

(* create anchors (vars with negative uid) for arguments of function *)
let init args =
  let get_anchor idx elm =
    FExp.BinOp ( Peq, Var (-(idx+1)), Var elm)
  in
  let pi = List.mapi get_anchor args in
  let f = {Formula.sigma = []; pi = pi} in
  {miss = f; act = f; lvars = []}

(* check if main is called with int argc and char **argv *)
(* TODO warnings handling *)
let check_main_args_type args =
  let arg1 = CL.Util.get_var (List.nth args 0) in
  let arg2 = CL.Util.get_var (List.nth args 1) in
  let arg1_typ = CL.Util.get_type arg1.typ in
  let arg1_ok = (match arg1_typ.code with
  | TypeInt -> true
  | _ -> prerr_endline "!!! warning: first argument of 'main' should be 'int'"; false) in
  let arg2_typ = CL.Util.get_type arg2.typ in
  let arg2_ok = (match arg2_typ.code with
    | TypePtr typ2 -> (let arg2_typ2 = CL.Util.get_type typ2 in
      match arg2_typ2.code with
      | TypePtr typ3 -> (let arg2_typ3 = CL.Util.get_type typ3 in
        match arg2_typ3.code with
        | TypeChar | TypeInt when arg2_typ3.size=1 -> true
        | _ -> prerr_endline "!!! warning: second argument of 'main' should be 'char **'"; false)
      | _ -> prerr_endline "!!! warning: second argument of 'main' should be 'char **'"; false)
    | _ -> prerr_endline "!!! warning: second argument of 'main' should be 'char **'"; false) in
  (arg1_ok && arg2_ok)

(* add anchors into LHS, if main(int argc, char **argv)
   MISS: arg1=argc & arg2=argv & arg2 -(l1)->Undef & (len(arg2)=l1) &
        (base(arg2)=arg2) & (0<=l1) & (l1=arg1*32)
   ACTUAL: arg1=argc & arg2=argv *)
let init_main args fuid =
  let num_args = List.length args in
  match num_args with
  | 0 -> empty
  | 2 -> (
    let anchor_state = init args in
    if not (check_main_args_type args) then
      anchor_state
    else
      let new_var = (CL.Util.list_max_positive (CL.Util.get_pvars fuid))+1 in
      let len = FExp.BinOp ( Peq, (UnOp (Len, Var (-2))), Var new_var) in
      let base = FExp.BinOp ( Peq, (UnOp (Base, Var (-2))), Var (-2)) in
      let size = FExp.BinOp ( Plesseq, FExp.zero, Var new_var) in
      let arg2 = CL.Util.get_var (List.nth args 1) in
      let ptr_size = CL.Util.get_type_size (arg2.typ) in
      let exp_ptr_size = FExp.Const (Int (Int64.of_int ptr_size)) in
      let block = FExp.BinOp ( Peq, Var new_var, (BinOp ( Pmult, Var (-1), exp_ptr_size))) in
      let sig_add = Formula.Hpointsto (Var (-2), Var new_var, Undef) in
      let new_miss =
        {Formula.pi = len :: base :: size :: block :: anchor_state.miss.pi;
        sigma = sig_add :: anchor_state.miss.sigma} in
      let s = {miss = new_miss; act = anchor_state.act; lvars = [new_var]} in
      print s; s)
  | _ -> prerr_endline "!!! warning: 'main' takes only zero or two arguments";
    init args (* handling as with an ordinary function *)

(* [substate fixed_vars state] contains in miss and act only clauses with
   variables from [fixed_vars] and related variables
   [state] - expect satisfiable state only
   [fixed_vars] - list of Exp, but expect CVar and Var only

   miss_vars = fixed_vars + related
   act_vars = fixed_vars + related from miss + related from act *)
(* TODO errors/warnings handling *)
let substate fixed_vars state =
  let get_lvar var =
    match var with
    | Formula.Exp.Var v when (List.mem v state.lvars) -> Some v
    | _ -> None
  in
  (* print_string ("\n" ^ CL.Util.list_to_string (Formula.Exp.to_string ~lvars:state.lvars) fixed_vars ^ "FIXED\n"); *)
  let (miss_removed_sigma,miss_vars,new_miss) =
    Formula.subformula fixed_vars state.miss in
  if (miss_removed_sigma)
  then raise RemovedSpatialPartFromMiss;
  (* print_string ("\n" ^ CL.Util.list_to_string (Formula.Exp.to_string ~lvars:state.lvars) miss_vars ^ "AFTER MISS\n"); *)
  let (act_removed_sigma,act_vars,new_act) =
    Formula.subformula miss_vars state.act in
  if (act_removed_sigma)
  then (if (Unix.isatty Unix.stderr) (* TODO more general *)
    then prerr_endline "\027[1;31m!!! MEMORY LEAK\027[0m"
    else prerr_endline "!!! MEMORY LEAK");
    (* print_string ("\n" ^ CL.Util.list_to_string (Formula.Exp.to_string ~lvars:state.lvars) act_vars ^ "AFTER ACT\n"); *)
  let all_vars = List.filter_map get_lvar (act_vars) in
  {miss = new_miss;
   act = new_act;
   lvars = all_vars}

let remove_equiv_vars gvars evars s =
  let rec rename_eqviv_vars evars state = 
    let equiv=Formula.get_varmap state.act.pi in
    match evars with
    | [] -> state
    | a :: rest ->
      let eq_vars=(Formula.get_eq_vars [a] equiv) in
      let notmem l x =
        let eq y= (x=y) in
        not (List.exists eq l)
      in
      let eq_vars_ex = List.filter (notmem gvars) eq_vars in 
      let todo_evars =  List.filter (notmem eq_vars) rest in 
      let act1 = Formula.substitute a eq_vars_ex state.act in
      let miss1 = Formula.substitute a eq_vars_ex state.miss in
      let lvars1 = List.filter (notmem eq_vars_ex) state.lvars in
      rename_eqviv_vars todo_evars {miss=miss1; act=act1; lvars=lvars1}
  in
  let s_rename = rename_eqviv_vars evars s in
  {miss= {pi = Formula.remove_redundant_eq s_rename.miss.pi; sigma = s_rename.miss.sigma};
  act= {pi = Formula.remove_redundant_eq s_rename.act.pi; sigma = s_rename.act.sigma};
  lvars=s_rename.lvars}

(* state - expect satisfiable state only *)
let simplify state =
  let mem lst x =
    let eq y= (x=y) in
    (List.exists eq lst )
  in
  let nomem lst x = not (mem lst x) in
  let vars = CL.Util.list_join_unique (Formula.find_vars state.act) (Formula.find_vars state.miss) in
  let used_lvars = List.filter (mem vars) state.lvars in
  let gvars = List.filter (nomem state.lvars) vars in
  let state0 = {miss=state.miss; act=state.act; lvars=used_lvars} in
  let state1 = remove_equiv_vars gvars used_lvars state0 in
  let miss_new = Formula.remove_useless_conjuncts state1.miss state1.lvars in
  (* logical variables used in miss_new can not be removed from act_new by means of remove_useless_conjuncts in order to preserve anchors 
     --- if miss_new contains l1 -- (8)-- >_ and act_new freed(l1) then freed(l1) can not be removed *)
  let lvars_unused_in_miss = List.filter (nomem (Formula.find_vars state.miss)) state1.lvars in
  let act_new= Formula.remove_useless_conjuncts state1.act lvars_unused_in_miss in
  {miss=miss_new; act=act_new; lvars=state1.lvars }

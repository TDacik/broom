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

type variable = Formula.Exp.variable

type t = { 
    miss: Formula.t;
    curr: Formula.t;
    lvars: variable list;
    through_loop: bool;
}

let empty = {
  miss = Formula.empty;
  curr = Formula.empty;
  lvars = [];
  through_loop = false}

let to_string state =
  "EXISTS: " ^ Formula.lvariables_to_string state.lvars
  ^ "\nMISS: " ^ Formula.to_string ~lvars:state.lvars state.miss
  ^ "\nCURR: " ^ Formula.to_string ~lvars:state.lvars state.curr
  
let print state =
  print_endline (to_string state)

let set_through_loop s = {
  miss = s.miss;
  curr = s.curr;
  lvars = s.lvars;
  through_loop = true}

(* gets unique variable uid for function defined by fuid *)
let get_fresh_lvar fuid lvars =
  (CL.Util.list_max_positive ((CL.Util.get_pvars fuid) @ lvars)) + 1

(* create anchors (vars with negative uid) for arguments of function *)
let init fuid =
  let get_anchor elm =
    FExp.BinOp ( Peq, Var (-elm), Var elm)
  in
  let pi = List.map get_anchor (CL.Util.get_anchors fuid) in
  let f = {Formula.sigma = []; pi = pi} in
  {miss = f; curr = f; lvars = []; through_loop = false}

(* check if main is called with int argc and char **argv *)
let check_main_args_type args loc =
  let arg1 = CL.Util.get_var (List.nth args 0) in
  let arg2 = CL.Util.get_var (List.nth args 1) in
  let arg1_typ = CL.Util.get_type arg1.typ in
  let arg1_ok = (match arg1_typ.code with
  | TypeInt -> true
  | _ -> Config.prerr_warn "first argument of 'main' should be 'int'" loc; false) in
  let arg2_typ = CL.Util.get_type arg2.typ in
  let arg2_ok = (match arg2_typ.code with
    | TypePtr typ2 -> (let arg2_typ2 = CL.Util.get_type typ2 in
      match arg2_typ2.code with
      | TypePtr typ3 -> (let arg2_typ3 = CL.Util.get_type typ3 in
        match arg2_typ3.code with
        | TypeChar | TypeInt when arg2_typ3.size=1 -> true
        | _ -> Config.prerr_warn "second argument of 'main' should be 'char **'" loc; false)
      | _ -> Config.prerr_warn "second argument of 'main' should be 'char **'" loc; false)
    | _ -> Config.prerr_warn "second argument of 'main' should be 'char **'" loc; false) in
  (arg1_ok && arg2_ok)

(* add anchors into LHS, if main(int argc, char **argv)
   MISS: arg1=argc & arg2=argv & arg2 -(l1)->Undef & (len(arg2)=l1) &
        (base(arg2)=arg2) & (0<=l1) & (l1=arg1*32)
   CURR: arg1=argc & arg2=argv *)
let init_main fuid =
  let args = CL.Util.get_fnc_args fuid in
  let num_args = List.length args in
  let loc = CL.Util.get_fnc_loc (CL.Util.get_fnc fuid) in
  match num_args with
  | 0 -> empty
  | 2 -> (
    let arg1_uid = (List.hd args) in
    let arg2_uid = (List.nth args 1) in
    let anchor_state = init fuid in
    if not (check_main_args_type args loc) then
      anchor_state
    else
      let new_var = get_fresh_lvar fuid [] in
      let len = FExp.BinOp ( Peq, (UnOp (Len, Var (-arg2_uid))), Var new_var) in
      let base = FExp.BinOp ( Peq, (UnOp (Base, Var (-arg2_uid))), Var (-arg2_uid)) in
      let size = FExp.BinOp ( Plesseq, FExp.zero, Var new_var) in
      let arg2 = CL.Util.get_var arg2_uid in
      let ptr_size = CL.Util.get_type_size (arg2.typ) in
      let exp_ptr_size = FExp.Const (Int (Int64.of_int ptr_size)) in
      let block = FExp.BinOp ( Peq, Var new_var, (BinOp ( Pmult, Var (-arg1_uid), exp_ptr_size))) in
      let sig_add = Formula.Hpointsto (Var (-arg2_uid), Var new_var, Undef) in
      let new_f =
        {Formula.pi = len :: base :: size :: block :: anchor_state.miss.pi;
        sigma = sig_add :: anchor_state.miss.sigma} in
      let s = {miss = new_f; curr = new_f; lvars = [new_var]; through_loop = false} in
      Config.debug3 (to_string s); s)
  | _ -> Config.prerr_warn  "'main' takes only zero or two arguments" loc;
    init fuid (* handling as with an ordinary function *)

let remove_equiv_vars gvars evars s =
  let rec rename_eqviv_vars evars state =
    match evars with
    | [] -> state
    | a :: rest ->
      let eq_vars=(Formula.get_equiv_vars [a] state.curr.pi) in
      let notmem l x =
        let eq y= (x=y) in
        not (List.exists eq l)
      in
      let eq_vars_ex = List.filter (notmem gvars) eq_vars in 
      let todo_evars =  List.filter (notmem eq_vars) rest in 
      let curr1 = Formula.substitute a eq_vars_ex state.curr in
      let miss1 = Formula.substitute a eq_vars_ex state.miss in
      let lvars1 = List.filter (notmem eq_vars_ex) state.lvars in
      rename_eqviv_vars todo_evars {miss=miss1; curr=curr1; lvars=lvars1; through_loop = state.through_loop}
  in
  let s_rename = rename_eqviv_vars evars s in
  {miss= {pi = Formula.remove_redundant_eq s_rename.miss.pi; sigma = s_rename.miss.sigma};
  curr= {pi = Formula.remove_redundant_eq s_rename.curr.pi; sigma = s_rename.curr.sigma};
  lvars=s_rename.lvars;
  through_loop = s_rename.through_loop}

(*
#mod_use "Formula.ml";;
#require "z3";;
#mod_use "Z3wrapper.ml";;
#mod_use "Abduction.ml";;
*)


open State
open Formula

(** contract *)
type contract = { 
    lhs: Formula.t;  
    rhs: Formula.t;  
    cvars: int list;
}

type contract_app_res =
| CAppOk of State.state
| CAppFail


let apply_contract ctx solv z3_names state c =
	match (Abduction.biabduction ctx solv z3_names state.act c.lhs) with
	| BFail -> CAppFail
	| Bok  (miss, fr) ->
		let missing= {pi=state.miss.pi @ miss.pi; sigma=state.miss.sigma @ miss.sigma } in
		let actual= {pi=fr.pi @ c.rhs.pi; sigma= fr.sigma @ c.rhs.sigma } in

		CAppOk {miss=missing; act=actual; lvars=state.lvars  }


(********************************************)
(* Experiments *)

let pre_move = {
    sigma = [ Hpointsto (Var 9, Var 10) ];
    pi = [ BinOp ( Peq, Var 9, Var 2332) ]
}
let post_move = {
    sigma = [ Hpointsto (Var 9, Var 10) ];
    pi = [ BinOp ( Peq, Var 10, Var 2332) ]
}

let c_move={lhs=pre_move; rhs=post_move; cvars=[9;10]};;

let pre_change = {
    sigma = [ Hpointsto (Var 9, Var 10) ];
    pi = [ BinOp ( Peq, Var 9, Var 2332);
	   BinOp ( Peq, Var 9,  UnOp ( Base, Var 9)) ]
}
let post_change = {
    sigma = [ Hpointsto (Var 9, Var 11) ];
    pi = [ BinOp ( Peq, Var 9, Var 2332); 
	   BinOp ( Peq, Var 9,  UnOp ( Base, Var 9)) ]
}

let c_change={lhs=pre_change; rhs=post_change; cvars=[9;10;11]};;




(*


let c_free={lhs=Formula.pre_free; rhs=Formula.post_free; cvars=[]};;
let s={miss={sigma=[];pi=[]};  act=Formula.form1; lvars=[1;2]}

open Z3
open Z3wrapper
let cfg = [("model", "true"); ("proof", "false")]
let ctx = (mk_context cfg)
let solv = (Solver.mk_solver ctx None)
let z3_names=get_sl_functions_z3 ctx




*)


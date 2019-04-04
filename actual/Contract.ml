(*
#mod_use "Formula.ml";;
#require "z3";;
#mod_use "Z3wrapper.ml";;
#mod_use "Abduction.ml";;
*)


open State

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

		CAppOk {miss=missing; miss_ex=state.miss_ex; act=actual; act_ex=state.act_ex  }



(* Experiments *)

(*


let c={lhs=Formula.pre_free; rhs=Formula.post_free; cvars=[]};;
let s={miss={sigma=[];pi=[]}; miss_ex=[]; act=Formula.form1; act_ex=[1;2]}

open Z3
open Z3wrapper
let cfg = [("model", "true"); ("proof", "false")]
let ctx = (mk_context cfg)
let solv = (Solver.mk_solver ctx None)
let z3_names=get_sl_functions_z3 ctx




*)


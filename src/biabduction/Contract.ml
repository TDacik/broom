(* module FExp = Formula.Exp *)

open CL.Operand
open CL.Fnc
open Formula

type formula = Formula.t
type variable = Exp.variable

type extend_formula = {
	f: formula;
	cnt_cvars: int;(* variable list; *)
	root: Exp.t; (* only Var/CVar *)
}

type t = {
    lhs: formula;
    rhs: formula;
    cvars: int; (* variable list; TODO: use int as number of cvars count from 1 *)
    pvarmap: (variable * variable) list;
}

(* let empty = {lhs = Formula.empty; rhs = Formula.empty; cvars = []; pvarmap = []} *)

let empty_exformula = {f = Formula.empty; cnt_cvars = 0; root = Undef}

let pvarmap_to_string pvarmap =
	CL.Util.list_to_string (fun (x,y) ->
		(Exp.variable_to_string x) ^ "->" ^ (Exp.variable_to_string y) )
		pvarmap

let to_string c =
  "Count of Contract local VARS: " ^ (* Formula.lvariables_to_string *) string_of_int c.cvars ^ "\n"
  ^ "LHS: " ^ Formula.to_string c.lhs ^ "\n"
  ^ "RHS: " ^ Formula.to_string c.rhs ^ "\n"
  ^ "Prog. VARS moves: " ^ pvarmap_to_string c.pvarmap ^ "\n"

let print c = print_string (to_string c)

(* var is Exp.t but only Var/CVar *)
let rec var_to_exformula var typ accs ef = (* empty_ext_formula *)
	match accs with
	| [] -> {f=ef.f; cnt_cvars=ef.cnt_cvars; root=var}
	| ac::tl -> (match ac.acc_data with
		| Ref ->
			let last_cvar = ef.cnt_cvars + 1 in
			let ptr_size = CL.Util.get_type_size typ(* ac.acc_typ *) in
			let exp_ptr_size = Exp.Const (Int (Int64.of_int ptr_size)) in
			let sig_add = [ Hpointsto (CVar last_cvar, exp_ptr_size, var) ] in
			var_to_exformula (CVar last_cvar) ac.acc_typ tl {f={sigma = ef.f.sigma @ sig_add; pi = ef.f.pi}; cnt_cvars=last_cvar; root=(CVar last_cvar)}
		| Deref ->
			let last_cvar = ef.cnt_cvars + 1 in
			let ptr_size = CL.Util.get_type_size typ(* ac.acc_typ *) in
			let exp_ptr_size = Exp.Const (Int (Int64.of_int ptr_size)) in
			let sig_add = [ Hpointsto (var, exp_ptr_size, CVar last_cvar) ] in
			var_to_exformula (CVar last_cvar) ac.acc_typ tl {f={sigma = ef.f.sigma @ sig_add; pi = ef.f.pi}; cnt_cvars=last_cvar; root=(CVar last_cvar)}
		| DerefArray _ (* idx *) -> assert false (* TODO *)
		| Item _ ->
			let cvar_obj = ef.cnt_cvars + 1 in (* find var in sigma *)
			let cvar_itm = cvar_obj + 1 in
			let cvar_last = cvar_itm + 1 in
			let (_,itm_off,itm_typ) = CL.Util.get_accessor_item ac in
			let pi_add = [ Exp.BinOp ( Peq, CVar cvar_itm,
			BinOp ( Pplus, CVar cvar_obj, Const (Int (Int64.of_int itm_off))));
			BinOp ( Peq, (UnOp (Base, CVar cvar_itm)), (UnOp (Base, CVar cvar_obj))) ] in
			let ptr_size_obj = CL.Util.get_type_size ac.acc_typ in
			let exp_ptr_size_obj = Exp.Const (Int (Int64.of_int ptr_size_obj)) in
			let ptr_size_itm = CL.Util.get_type_size itm_typ in
			let exp_ptr_size_itm = Exp.Const (Int (Int64.of_int ptr_size_itm)) in
			let sig_add = [ Hpointsto (CVar cvar_obj, exp_ptr_size_obj, var);
			Hpointsto (CVar cvar_itm, exp_ptr_size_itm, CVar cvar_last) ] in
			var_to_exformula (CVar cvar_last) ac.acc_typ tl {f={sigma = ef.f.sigma @ sig_add; pi = ef.f.pi @ pi_add}; cnt_cvars=cvar_last; root=(CVar cvar_last)}
		| Offset off ->
			let last_cvar = ef.cnt_cvars + 1 in
			let pi_add = [ Exp.BinOp ( Peq, CVar last_cvar,
			BinOp ( Pplus, var, Const (Int (Int64.of_int off)))) ] in
			var_to_exformula (CVar last_cvar) ac.acc_typ tl {f={sigma = ef.f.sigma; pi = ef.f.pi @ pi_add};cnt_cvars=last_cvar; root=(CVar last_cvar)} )

let constant_to_exformula data accs ef =
	if (accs != []) then assert false;
	let pi_add = (match data with
	| CstPtr i -> Exp.Const (Ptr i)
	| CstInt i -> Const (Int i)
	| CstEnum i -> Const (Int (Int64.of_int i))
	| CstChar i -> Const (Int (Int64.of_int (Char.code i)))
	| CstBool b -> Const (Bool b)
	| CstReal r -> Const (Float r)
	| CstString str -> Const (String str)
	| CstStruct | CstUnion | CstArray | CstFnc _ -> assert false) in
	{f=ef.f; cnt_cvars = ef.cnt_cvars; root = pi_add}

let operand_to_exformula op ef =
	match op.data with
		| OpVar uid -> var_to_exformula (Var uid) op.typ op.accessor ef
		| OpCst { cst_data } -> constant_to_exformula cst_data op.accessor ef
		| OpVoid -> assert false

let contract_for_assign dst src =
	let ef_dst = operand_to_exformula dst empty_exformula in
	let ef_src = operand_to_exformula src {f=ef_dst.f; cnt_cvars=ef_dst.cnt_cvars; root=Undef} in
	let lhs = ef_src.f in
	let assign = Exp.BinOp ( Peq, ef_dst.root, ef_src.root) in
	let rhs = {pi = assign :: lhs.pi; sigma = lhs.sigma} in
	{lhs = lhs; rhs = rhs; cvars = ef_src.cnt_cvars; pvarmap = []}

let get_contract insn =
	match insn.code with
	(* | InsnRET ret -> []
	| InsnCLOBBER var -> []
	| InsnABORT -> []
	| InsnBINOP (code, dst, src1, src2) -> []
	| InsnCALL ops -> [] *)
	| InsnUNOP (code, dst, src) -> (match code with
		| CL_UNOP_ASSIGN -> (contract_for_assign dst src)::[]
		| _ -> [] )
	| InsnNOP | InsnJMP _ | InsnCOND _ | InsnLABEL _ -> []
	| InsnSWITCH _ -> assert false
	| _ -> []


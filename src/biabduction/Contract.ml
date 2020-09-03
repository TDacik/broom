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
    cvars: int;
    pvarmap: (variable * variable) list;
}

let empty_exformula = {f = Formula.empty; cnt_cvars = 0; root = Undef}

let empty = {lhs = Formula.empty; rhs = Formula.empty; cvars = 0; pvarmap = []}

let pvarmap_to_string pvarmap =
	CL.Util.list_to_string (fun (x,y) ->
		(Exp.variable_to_string x) ^ "->" ^ (Exp.cvariable_to_string y) )
		pvarmap

let to_string c =
  "Count of Contract local VARS: " ^ string_of_int c.cvars ^ "\n"
  ^ "LHS: " ^ Formula.to_string c.lhs ^ "\n"
  ^ "RHS: " ^ Formula.to_string c.rhs ^ "\n"
  ^ "Prog. VARS moves: " ^ pvarmap_to_string c.pvarmap

let print c = print_endline (to_string c)

(* var is Exp.t but only Var/CVar, last C represents root
   returns tuple (debub_string, ef) where debug_string contains the order of
   applying accessors rules *)
let rec var_to_exformula var accs ef = (* empty_ext_formula *)
	match accs with
	| [] -> ("", {f=ef.f; cnt_cvars=ef.cnt_cvars; root=var})
	| ac::tl -> (match ac.acc_data with

		(* C -()-> <var> *)
		| Ref ->
			let (obj,cvars_obj) = find_var_pointsto var ef.f.sigma ef.cnt_cvars in
			let ptr_size = CL.Util.get_type_size ac.acc_typ in
			let exp_ptr_size = Exp.Const (Int (Int64.of_int ptr_size)) in
			let (sig_add, dbg_add) =
				if ef.cnt_cvars = cvars_obj then (* points-to exists *)
					([], "Ref2, ")
				else
					([ Hpointsto (obj, exp_ptr_size, var) ],"Ref1, ") in
			let (dbg, ef_new) = var_to_exformula obj tl
				{f={sigma = ef.f.sigma @ sig_add; pi = ef.f.pi};
				cnt_cvars=cvars_obj;
				root=obj} in
			(dbg_add ^ dbg, ef_new)

		(* <var> -()-> C *)
		| Deref ->
			let last_cvar = ef.cnt_cvars + 1 in
			let ptr_typ = CL.Util.get_type_ptr ac.acc_typ in
			let ptr_size = CL.Util.get_type_size ptr_typ in
			let exp_ptr_size = Exp.Const (Int (Int64.of_int ptr_size)) in
			let sig_add = [ Hpointsto (var, exp_ptr_size, CVar last_cvar) ] in
			let (dbg, ef_new) = var_to_exformula (CVar last_cvar) tl
				{f={sigma = ef.f.sigma @ sig_add; pi = ef.f.pi};
				cnt_cvars=last_cvar;
				root=(CVar last_cvar)} in
			("Deref, " ^ dbg, ef_new)

		| DerefArray _ (* idx *) -> assert false (* TODO *)

		(* from: C1 -()-> <var>
		   to: C2-()->C & C2 = C1 + item & base(C2)=base(C1)*)
		| Item _ ->
			let (obj,cvars_obj) = find_var_pointsto var ef.f.sigma ef.cnt_cvars in
			assert (ef.cnt_cvars = cvars_obj); (* TODO object on stack unsupported *)

			(* let cvar_obj = ef.cnt_cvars + 1 in (* find var in sigma *) *)
			let cvar_itm = cvars_obj + 1 in
			let cvar_last = cvar_itm + 1 in
			let (_,itm_off,itm_typ) = CL.Util.get_accessor_item ac in
			let field = (if (itm_off != 0)
			then
				Exp.BinOp ( Peq, CVar cvar_itm, BinOp ( Pplus, obj, Const (Int (Int64.of_int itm_off))))
			else
				Exp.BinOp ( Peq, CVar cvar_itm, obj)) in
			let pi_add = [ field;
			BinOp ( Peq, (UnOp (Base, CVar cvar_itm)), (UnOp (Base, obj))) ] in
			(* let exp_obj = (match obj with (* move to LHS only! *)
				| CVar _ ->
					let ptr_size_obj = CL.Util.get_type_size ac.acc_typ in
					let exp_ptr_size_obj = Exp.Const (Int (Int64.of_int ptr_size_obj)) in
					[ Hpointsto (obj, exp_ptr_size_obj, var) ]
				| _ -> [] ) in *)
			let ptr_size_itm = CL.Util.get_type_size itm_typ in
			let exp_ptr_size_itm = Exp.Const (Int (Int64.of_int ptr_size_itm)) in
			let sig_add = [ Hpointsto (CVar cvar_itm, exp_ptr_size_itm, CVar cvar_last) ] in
			let (dbg, ef_new) = var_to_exformula (CVar cvar_last) tl
				{f={sigma = (* exp_obj @ *) sig_add; pi = ef.f.pi @ pi_add};
				cnt_cvars=cvar_last;
				root=(CVar cvar_last)} in
			("Record acc, " ^ dbg, ef_new)

		(* from: C1 -(1)-> <var>
		   to: C2 -(1)-> C & C2 = C1 + off *)
		| Offset off ->
			let (obj,cvars_obj) = find_var_pointsto var ef.f.sigma ef.cnt_cvars in
			assert (ef.cnt_cvars = cvars_obj); (* TODO object on stack unsupported *)
			let cvar_elm = cvars_obj + 1 in
			let cvar_last = cvar_elm + 1 in
			let const_off = Exp.Const (Int (Int64.of_int off)) in
			let elm = Exp.BinOp ( Peq, CVar cvar_elm, BinOp ( Pplus, obj, const_off)) in
			let pi_add = [ elm;
			BinOp ( Peq, (UnOp (Base, CVar cvar_elm)), (UnOp (Base, obj))) ] in
			let ptr_size = CL.Util.get_type_size ac.acc_typ in
			let exp_ptr_size = Exp.Const (Int (Int64.of_int ptr_size)) in
			let sig_add = [ Hpointsto (CVar cvar_elm, exp_ptr_size, CVar cvar_last) ] in
			let (dbg, ef_new) = var_to_exformula (CVar cvar_last) tl
				{f={sigma = sig_add; pi = ef.f.pi @ pi_add};
				cnt_cvars=cvar_last;
				root=(CVar cvar_last)} in
			("Offset, " ^ dbg, ef_new)
		)

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
		| OpVar uid ->
			let (dbg, ef_new) = var_to_exformula (Var uid) op.accessor ef in
			(if (dbg <> "")
			then print_string ("OP \""^(CL.Printer.operand_to_string op)^"\": "^dbg));
			ef_new
		| OpCst { cst_data } -> constant_to_exformula cst_data op.accessor ef
		| OpVoid -> ef

(* return tuple (args,ef) where args is list of arguments and ef is formula
   describing all arguments *)
let rec args_to_exformula args ef =
  match args with
  | [] -> ([], ef)
  | arg::tl -> let ef_arg = operand_to_exformula arg ef in
    let (roots,all_ef) = args_to_exformula tl ef_arg in
    ((ef_arg.root)::roots, all_ef)

(* SUBCONTRACT *)

(* subcontract contains in lhs and rhs only clauses with variables from vars
   and related variables
   doesn't reduce count of contract variables
   vars - list of Exp, but expect CVar and Var only *)
(* FIXME not removes false predicates *)
(* FIXME vars should contain Xs from moves (_->X) *)
let rec subcontract vars c =
	match vars with
	| [] -> empty
	| _ ->
		let (_,lhs_vars,new_lhs) = subformula vars c.lhs in
		let (_,rhs_vars,new_rhs) = subformula vars c.rhs in
		(* FIXME removing spatial part ignored *)
		let tl_c = subcontract (CL.Util.list_join_unique lhs_vars rhs_vars)
			{lhs = (Formula.diff c.lhs new_lhs);
			 rhs = (Formula.diff c.rhs new_rhs);
			 cvars = c.cvars;
			 pvarmap = c.pvarmap} in
		{lhs = Formula.disjoint_union new_lhs tl_c.lhs;
		 rhs = Formula.disjoint_union new_rhs tl_c.rhs;
		 cvars = c.cvars;
		 pvarmap = c.pvarmap}

(* CREATING CONTRACTS *)

(* replace dst, return new dst and pvarmap for contract *)
let rewrite_dst dst =
	match dst.root with
	| Exp.Var puid -> let cuid = dst.cnt_cvars + 1 in
		({f = dst.f; cnt_cvars = cuid; root = Exp.CVar cuid}, [(puid, cuid)])
	| CVar old_cuid -> let cuid = dst.cnt_cvars + 1 in
		let new_f = substitute_vars_cvars (CVar cuid) (CVar old_cuid) dst.f in
		({f = new_f; cnt_cvars = cuid; root = Exp.CVar cuid}, [])
	| _ -> (dst, [])

(* return value in special contract variable with uid 0 *)
let contract_for_ret ret =
	let ef_ret = operand_to_exformula ret empty_exformula in
	match ef_ret.root with
	| Exp.Undef -> []
	| _ -> (
		let lhs = ef_ret.f in
		let assign = Exp.BinOp ( Peq, Exp.ret, ef_ret.root) in
		let rhs = {pi = assign :: lhs.pi; sigma = lhs.sigma} in
		[{lhs = lhs; rhs = rhs; cvars = ef_ret.cnt_cvars; pvarmap = []}] )

let contract_fail =
	let rhs = {pi = (Const (Bool false))::[]; sigma = []} in
	{lhs = Formula.empty; rhs = rhs; cvars = 0; pvarmap = []}

(* 1st contract is for then branch, 2nd for else branch *)
let contract_for_cond op =
	let ef_op = operand_to_exformula op empty_exformula in
	let assign_then = Exp.BinOp ( Peq, ef_op.root, Const (Bool true) ) in
	let assign_else = Exp.BinOp ( Peq, ef_op.root, Const (Bool false) ) in
	let lhs_then = {pi = assign_then :: ef_op.f.pi; sigma = ef_op.f.sigma} in
	let lhs_else = {pi = assign_else :: ef_op.f.pi; sigma = ef_op.f.sigma} in
	let c1 = {lhs = lhs_then; rhs = lhs_then; cvars = ef_op.cnt_cvars; pvarmap = []} in
	let c2 = {lhs = lhs_else; rhs = lhs_else; cvars = ef_op.cnt_cvars; pvarmap = []} in
	c1::c2::[]

(****** CONTRACTS FOR BINARY OPERATION ******)

(* binary operators for comparison: (==, !=), (<, >=), (>, <=) generate 2
   contracts: one with operator and second with opposite operator in LHS *)
let contract_for_binop code dst src1 src2 =
	let ef_dst = operand_to_exformula dst empty_exformula in
	let ef_src1 = operand_to_exformula src1 {f=ef_dst.f; cnt_cvars=ef_dst.cnt_cvars; root=Undef} in
	let ef_src2 = operand_to_exformula src2 {f=ef_src1.f; cnt_cvars=ef_src1.cnt_cvars; root=Undef} in
	let lhs = ef_src2.f in
	let (new_dst, pvarmap) = rewrite_dst {f=ef_src2.f; cnt_cvars=ef_src2.cnt_cvars; root=ef_dst.root} in
	let bin_exp = ( match code with
		| CL_BINOP_EQ -> [Exp.BinOp ( Peq, ef_src1.root, ef_src2.root);
			BinOp ( Pneq, ef_src1.root, ef_src2.root)]
		| CL_BINOP_NE -> [BinOp ( Pneq, ef_src1.root, ef_src2.root);
			BinOp ( Peq, ef_src1.root, ef_src2.root)]
		| CL_BINOP_LT -> [BinOp ( Pless, ef_src1.root, ef_src2.root);
			BinOp ( Plesseq, ef_src2.root, ef_src1.root)]
		| CL_BINOP_GT -> [BinOp ( Pless, ef_src2.root, ef_src1.root);
			BinOp ( Plesseq, ef_src1.root, ef_src2.root)]
		| CL_BINOP_LE -> [BinOp ( Plesseq, ef_src1.root, ef_src2.root);
			BinOp ( Pless, ef_src2.root, ef_src1.root)]
		| CL_BINOP_GE -> [BinOp ( Plesseq, ef_src2.root, ef_src1.root);
			BinOp ( Pless, ef_src1.root, ef_src2.root)]
		| CL_BINOP_TRUTH_AND -> [BinOp ( Pand, ef_src1.root, ef_src2.root)]
		| CL_BINOP_TRUTH_OR -> [BinOp ( Por, ef_src1.root, ef_src2.root)]
		| CL_BINOP_TRUTH_XOR -> [BinOp ( Pxor, ef_src1.root, ef_src2.root)]
		| CL_BINOP_PLUS | CL_BINOP_POINTER_PLUS ->
			[BinOp ( Pplus, ef_src1.root, ef_src2.root)]
		| CL_BINOP_MINUS -> [BinOp ( Pminus, ef_src1.root, ef_src2.root)]
		| CL_BINOP_MULT -> [BinOp ( Pmult, ef_src1.root, ef_src2.root)]
		| CL_BINOP_EXACT_DIV | CL_BINOP_TRUNC_DIV ->
			[BinOp ( Pdiv, ef_src1.root, ef_src2.root)]
		| CL_BINOP_TRUNC_MOD -> [BinOp ( Pmod, ef_src1.root, ef_src2.root)]
		| CL_BINOP_BIT_AND -> [BinOp ( BVand, ef_src1.root, ef_src2.root)]
		| CL_BINOP_BIT_IOR -> [BinOp ( BVor, ef_src1.root, ef_src2.root)]
		| CL_BINOP_BIT_XOR -> [BinOp ( BVxor, ef_src1.root, ef_src2.root)]
		| CL_BINOP_LSHIFT -> [BinOp ( BVlshift, ef_src1.root, ef_src2.root)]
		| CL_BINOP_RSHIFT -> [BinOp ( BVrshift, ef_src1.root, ef_src2.root)]
		| CL_BINOP_LROTATE -> [BinOp ( BVlrotate, ef_src1.root, ef_src2.root)]
		| CL_BINOP_RROTATE -> [BinOp ( BVrrotate, ef_src1.root, ef_src2.root)]
		| _ -> [Undef] (* TODO: should be Def or Everything *)
	) in
	let assign = Exp.BinOp ( Peq, new_dst.root, (List.hd bin_exp) ) in
	match bin_exp with
	| [_] ->
		let pi_add = ( match code with
			| CL_BINOP_POINTER_PLUS -> [ assign; Exp.BinOp ( Plesseq,
				 new_dst.root,
				 BinOp ( Pplus,
					 UnOp (Base, new_dst.root),
					 UnOp (Len, new_dst.root))
				 ) ]
			| CL_BINOP_EXACT_DIV | CL_BINOP_TRUNC_DIV | CL_BINOP_TRUNC_MOD ->
				[ assign; Exp.BinOp ( Pneq, ef_src2.root, Exp.zero )]
			| _ -> [assign]
		) in
		let rhs = {pi = pi_add @ new_dst.f.pi; sigma = new_dst.f.sigma} in
		[{lhs = lhs; rhs = rhs; cvars = new_dst.cnt_cvars; pvarmap = pvarmap}]
	| e1::e2::[] ->
		let lhs1 = {pi = e1::lhs.pi; sigma = lhs.sigma} in
		let rhs1 = {pi = assign::e1::new_dst.f.pi; sigma = new_dst.f.sigma} in
		let lhs2 = {pi = e2::lhs.pi; sigma = lhs.sigma} in
		let rhs2 = {pi = assign::e2::new_dst.f.pi; sigma = new_dst.f.sigma} in
		[{lhs=lhs1; rhs=rhs1; cvars=new_dst.cnt_cvars; pvarmap=pvarmap};
		 {lhs=lhs2; rhs=rhs2; cvars=new_dst.cnt_cvars; pvarmap=pvarmap}]
	| _ -> assert false

(****** CONTRACTS FOR UNARY OPERATION ******)

let contract_for_unop code dst src =
	let ef_dst = operand_to_exformula dst empty_exformula in
	let ef_src = operand_to_exformula src {f=ef_dst.f; cnt_cvars=ef_dst.cnt_cvars; root=Undef} in
	let lhs = ef_src.f in
	let (new_dst, pvarmap) = rewrite_dst {f=ef_src.f; cnt_cvars=ef_src.cnt_cvars; root=ef_dst.root} in
	let un_exp = ( match code with
		| CL_UNOP_ASSIGN -> ef_src.root
		| CL_UNOP_BIT_NOT -> Exp.UnOp ( BVnot, ef_src.root)
		| CL_UNOP_TRUTH_NOT -> Exp.UnOp ( Pnot, ef_src.root)
		| CL_UNOP_MINUS -> Exp.UnOp ( Puminus, ef_src.root)
		| _ -> Undef (* TODO: should be Def or Everything *)
	) in
	let assign = Exp.BinOp ( Peq, new_dst.root, un_exp ) in
	let rhs = {pi = assign :: new_dst.f.pi; sigma = new_dst.f.sigma} in
	{lhs = lhs; rhs = rhs; cvars = new_dst.cnt_cvars; pvarmap = pvarmap}

(****** CONTRACTS FOR BUILT-IN FUNCTIONS ******)

(*
   if size<0 or unsuccesful alloc : dst=null
   else         len(dst)=size & base(dst)=dst & dst-(size)->undef
   allowd create object of size 0
   TODO: if size is constant, don't generate 0<=size
*)
let contract_for_malloc dst size =
	let ef_dst = operand_to_exformula dst empty_exformula in
	let ef_size = operand_to_exformula size {f=ef_dst.f; cnt_cvars=ef_dst.cnt_cvars; root=Undef} in
	let lhs = ef_size.f in
	let (new_dst, pvarmap) = rewrite_dst {f=ef_size.f; cnt_cvars=ef_size.cnt_cvars; root=ef_dst.root} in
	let len = Exp.BinOp ( Peq, (UnOp (Len, new_dst.root)), ef_size.root) in
	let base = Exp.BinOp ( Peq, (UnOp (Base, new_dst.root)), new_dst.root) in
	let size = Exp.BinOp ( Plesseq, Exp.zero, ef_size.root) in
	let sig_add = Hpointsto (new_dst.root, ef_size.root, Undef) in
	let rhs =
		{pi = len :: base :: size :: new_dst.f.pi;
		sigma = sig_add :: new_dst.f.sigma} in
	{lhs = lhs; rhs = rhs; cvars = new_dst.cnt_cvars; pvarmap = pvarmap}

(* PRE: base(src)=src POS: freed(src)
   PRE: src=NULL      POS:
*)
let contract_for_free src =
	let ef_src = operand_to_exformula src empty_exformula in
	let lhs = ef_src.f in
	(* let len = Exp.BinOp ( Peq, (UnOp (Len, ef_src.root)), Undef) in *)
	let sig_add = Hpointsto (ef_src.root, Exp.one, Undef) in
	let base = Exp.BinOp ( Peq, (UnOp (Base, ef_src.root)), ef_src.root) in
	(* let not_freed_pi = Exp.UnOp ( Pnot, (UnOp (Freed, ef_src.root))) in *)
	let freed_pi = Exp.UnOp (Freed, ef_src.root) in
	let c1 = {lhs = {pi = base :: lhs.pi; sigma = sig_add :: lhs.sigma};
		      rhs = {pi = freed_pi :: lhs.pi; sigma = lhs.sigma};
		      cvars = ef_src.cnt_cvars;
		      pvarmap = []} in
	let null_pi = Exp.BinOp ( Peq, ef_src.root, Exp.null) in
	let c2 = {lhs = {pi = null_pi :: lhs.pi; sigma = lhs.sigma};
		      rhs = Formula.empty;
		      cvars = ef_src.cnt_cvars;
		      pvarmap = []} in
	c1::c2::[]

let contract_nondet dst =
	match dst.data with
	| OpVoid -> []
	| _ ->
		let ef_dst = operand_to_exformula dst empty_exformula in
		let lhs = ef_dst.f in
		let (new_dst, pvarmap) = rewrite_dst ef_dst in
		let assign = Exp.BinOp ( Peq, new_dst.root, Undef) in
		let rhs = {pi = assign :: new_dst.f.pi; sigma = new_dst.f.sigma} in
		{lhs = lhs; rhs = rhs; cvars = new_dst.cnt_cvars; pvarmap = pvarmap}::[]

let contract_for_builtin dst called args =
	let fnc_name = CL.Printer.operand_to_string called in
	match fnc_name, args with
	| "abort", [] -> (contract_fail)::[]
	| "malloc", size::[] -> (contract_for_malloc dst size)::[]
	| "free", src::[] -> contract_for_free src
	| "__VERIFIER_error", [] -> (contract_fail)::[]
	| "__VERIFIER_nondet_int", [] -> contract_nondet dst
	| "__VERIFIER_nondet_unsigned", [] -> contract_nondet dst (* TODO: 0..MAX *)
	| "rand", [] -> contract_nondet dst (* TODO: 0..MAX *)
	| _,_ -> [] (* TODO: unrecognized built-in/extern function *)

(****** CONTRACTS CALLED FUNCTIONS ******)

(* roots - aguments of called function in reverse order
   vars - parameters of called function *)
let rec substitute_arguments roots num f =
	match roots,num with
	| [],0 -> f
	| root::rtl,num when num>0 ->
		let subf = substitute_vars_cvars root (Var (-num)) f in
		substitute_arguments rtl (num-1) subf
	| _,_ -> assert false (* TODO: variable number of arguments unsupported *)

(* rename dst and args in given contract c;
   dst and args (TODO) could be rewritten in rhs *)
(* TODO: first 3 lines should be as argumets and called from outside *)
let contract_for_called_fnc dst args num_args c =
	let ef_init = {f = Formula.empty; cnt_cvars = c.cvars; root = Undef} in
	let ef_dst = operand_to_exformula dst ef_init in
	let (roots,ef_args) = args_to_exformula args ef_dst in
	let roots_rev = List.rev roots in
	let new_lhs = substitute_arguments roots_rev num_args c.lhs in

	let (new_dst, pvarmap) = rewrite_dst {f=Formula.empty; cnt_cvars=ef_args.cnt_cvars; root=ef_dst.root} in
	let dst_rhs = substitute_vars_cvars new_dst.root (Exp.ret) c.rhs in
	let new_rhs = substitute_arguments roots_rev num_args dst_rhs in
	{
		lhs = {sigma = new_lhs.sigma @ ef_args.f.sigma;
			pi = new_lhs.pi @ ef_args.f.pi};
		rhs = new_rhs;
		cvars = new_dst.cnt_cvars;
		pvarmap = pvarmap
	}


let get_contract insn =
	match insn.code with
	| InsnRET ret -> contract_for_ret ret
	| InsnCOND (op,_,_) -> contract_for_cond op
	(* | InsnCLOBBER var -> [] *)
	| InsnABORT -> (contract_fail)::[]
	| InsnBINOP (code, dst, src1, src2) -> contract_for_binop code dst src1 src2
	| InsnCALL ops -> ( match ops with
		| dst::called::args -> if (CL.Util.is_extern called)
			then contract_for_builtin dst called args
			else []
		| _ -> assert false )
	| InsnUNOP (code, dst, src) -> (contract_for_unop code dst src)::[]
	| InsnNOP | InsnJMP _ | InsnLABEL _ -> []
	| InsnSWITCH _ -> assert false
	| _ -> []

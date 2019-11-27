(* Pretty printer for Code Listener Storage *)

open Operand
open Var
open Fnc

type uid = int

(* TODO: use exceptions *)

(* internal location *)
#define ILOC (Printf.sprintf "%s:%i" __FILE__ __LINE__)

let error loc msg = Printf.eprintf "%s: error: %s\n" loc msg

let empty_output = Printf.printf ""




let loc_to_string loc =
	match loc with
	| Some (file, line, column, _) ->
		Printf.sprintf "%s:%i:%i: " file line column
	| None -> ""

(* TODO type *)
let type_to_string _ (* uid *) = ""

let var_to_string uid =
	let v = Util.get_var uid in
	let uid_str = Printf.sprintf "%i" uid in
	let scope = (match v.code with
		| VAR_GL -> "S"
		| VAR_LC -> "F"
		| _ -> "") in
	match v.name with
		| Some name ->  "%m" ^ scope ^ uid_str ^ ":" ^ name
		| None -> "%r" ^ scope ^ uid_str

(* Get CL operand as string *)
let rec operand_to_string op =
	match op.Operand.data with
		| OpVar uid -> op_var_to_string uid op.accessor
		| OpCst { cst_data } -> constant_to_string cst_data op.accessor
		| OpVoid -> "void"

(* TODO: structure acc -> *)
and back_accessors accs =
	match accs with
	| [] -> ""
	(* | fst::snd::tl -> (match fst.acc_data with
		| Deref -> (match snd.acc_data) with
			| Item uid -> "->"; back_accessors snd::tl )
		| _ -> ) *)
	| ac::tl -> (match ac.acc_data with
		| DerefArray idx -> let rest = back_accessors tl in 
			let str_idx = operand_to_string idx in
			"[" ^ str_idx ^ "]" ^ rest
		| Item _ (* uid *) -> let rest = back_accessors tl in
			"." ^ rest
		| Ref -> error ILOC "invalid reference accessor"; "&"
		| _ -> error ILOC "unsupported accessor"; "")

and middle_var uid accs =
	let var = var_to_string uid in
	let rest = back_accessors accs in
		var ^ rest

and front_accessors uid accs =
	match accs with
	| [] -> middle_var uid []
	| ac::tl -> ( match ac.acc_data with
		| Ref -> let rest = front_accessors uid tl in "&" ^ rest
		| Deref -> let rest = front_accessors uid tl in "*" ^ rest
		| _ -> middle_var uid (ac::tl) )

and op_var_to_string uid accs =
	front_accessors uid accs

and const_ptr_to_string ptr accs =
	let str_acc = ( match accs with
		| [] -> ""
		| ac::[] -> ( match ac.acc_data with
			| Deref -> "*"
			| _ -> error ILOC "unexpected accessor by constant pointer"; "" )
		| _ -> error ILOC "too much accessors by constant pointer"; "" ) in
	if ptr==0 then "NULL" else Printf.sprintf "%s0x%x" str_acc ptr

and constant_to_string data accs =
	match data with
	| CstPtr ptr -> const_ptr_to_string ptr accs
	| CstStruct | CstUnion | CstArray ->
		error ILOC "unsupported compound literal"; "?"
	| CstFnc fnc -> ( match fnc.name with
		| Some x -> x
		| None -> error ILOC "anonymous function"; "" )
	| CstInt i -> Int64.to_string i                 (* TODO: test unsigned *)
	| CstEnum e -> Printf.sprintf "%i" e            (* TODO: test unsigned *)
	| CstChar c -> "\'" ^ Printf.sprintf "%c" c ^ "\'"
	| CstBool b -> Printf.sprintf "%B" b
	| CstReal f -> Printf.sprintf "%g" f
	| CstString str -> "\"" ^ String.escaped str ^ "\""



let get_fnc_name f = operand_to_string f.Fnc.def

(* Print unary CL instruction *)
let print_unary_insn code dst src =
	let unop = ( match code with
		| CL_UNOP_TRUTH_NOT -> "!"
		| CL_UNOP_BIT_NOT -> "~"
		| CL_UNOP_MINUS -> "-"
		| CL_UNOP_ABS -> "abs("
		| CL_UNOP_FLOAT -> "(float) "
		| _ -> "") in
	let e = (match code with
		| CL_UNOP_ABS -> ")"
		| _ -> "") in
	let str_dst = operand_to_string dst in
	let str_src = operand_to_string src in
		Printf.printf "\t\t%s := %s%s%s\n" str_dst unop str_src e

(* Print binary CL instruction *)
let print_binary_insn code dst src1 src2 =
	let binop = ( match code with
		| CL_BINOP_EQ -> "=="
		| CL_BINOP_NE -> "!="
		| CL_BINOP_LT -> "<"
		| CL_BINOP_GT -> ">"
		| CL_BINOP_LE -> "<="
		| CL_BINOP_GE -> ">="
		| CL_BINOP_TRUTH_AND -> "&&"
		| CL_BINOP_TRUTH_OR -> "||"
		| CL_BINOP_TRUTH_XOR -> "xor"
		| CL_BINOP_PLUS -> "+"
		| CL_BINOP_MINUS -> "-"
		| CL_BINOP_MULT -> "*"
		| CL_BINOP_EXACT_DIV | CL_BINOP_TRUNC_DIV | CL_BINOP_RDIV -> "/"
		| CL_BINOP_TRUNC_MOD -> "%"
		| CL_BINOP_MIN -> "min"
		| CL_BINOP_MAX -> "max"
		| CL_BINOP_POINTER_PLUS -> "[ptr]+"
		| CL_BINOP_BIT_AND -> "&"
		| CL_BINOP_BIT_IOR -> "|"
		| CL_BINOP_BIT_XOR -> "^"
		| CL_BINOP_LSHIFT -> "<<"
		| CL_BINOP_RSHIFT -> ">>"
		| CL_BINOP_LROTATE -> "lrotate"
		| CL_BINOP_RROTATE -> "rrotate"
		| CL_BINOP_UNKNOWN -> "?") in
	let str_dst = operand_to_string dst in
	let str_src1 = operand_to_string src1 in
	let str_src2 = operand_to_string src2 in
		Printf.printf "\t\t%s := (%s %s %s)\n" str_dst str_src1 binop str_src2

(* Print list of elms separated by ',' calling 'to_string' on each elm *)
let rec print_list to_string args =
	match args with
	| [] -> ()
	| lst::[] -> let str_arg = to_string lst in
		Printf.printf "%s" str_arg
	| hd::tl ->  let str_arg = to_string hd in 
		Printf.printf "%s, " str_arg;
		print_list to_string tl

(* Print call instruction; ops = dst, called, ?args+ *)
let print_call_insn ops =
	match ops with
	| hd::snd::args ->
		let str_called = operand_to_string snd in
		if not (Util.is_void hd)
			then let str_dst = operand_to_string hd in
				Printf.printf "\t\t%s := " str_dst
			else Printf.printf "\t\t";
		Printf.printf "%s(" str_called;
		print_list operand_to_string args;
		Printf.printf ")\n"
	| _ -> error ILOC "wrong call instruction"

(* Print CL instruction *)
let print_insn insn =
	match insn.code with
	| InsnNOP -> Printf.printf "\t\tnop\n"
	| InsnJMP uid -> Printf.printf "\t\tgoto L%i\n" uid
	| InsnCOND (cond, tg_then, tg_else) -> let op = operand_to_string cond in
		Printf.printf "\t\tif (%s)\n\t\t\tgoto L%i\n\t\telse\n\t\t\tgoto L%i\n"  op tg_then tg_else
	| InsnRET ret -> if not (Util.is_void ret)
		then let op = operand_to_string ret in
			Printf.printf "\t\treturn %s\n" op
		else Printf.printf "\t\treturn\n"
	| InsnCLOBBER var -> let op = operand_to_string var in
		Printf.printf "\t\tclobber %s\n" op
	| InsnABORT -> Printf.printf "\t\tabort\n"
	| InsnUNOP (code, dst, src) -> print_unary_insn code dst src
	| InsnBINOP (code, dst, src1, src2) -> print_binary_insn code dst src1 src2
	| InsnCALL ops -> print_call_insn ops
	| InsnSWITCH _ -> error ILOC "unsupported switch instruction"
	| InsnLABEL _ -> empty_output (* unused *)

let print_block apply_on bb =
	Printf.printf "\tL%i:\n" bb.uid;
	List.iter apply_on bb.insns

let rec print_cfg apply_on_insn cfg =
	match cfg with
	| [] -> ()
	| bb::tl -> print_block apply_on_insn bb; print_cfg apply_on_insn tl

(* Print function *)
let print_fnc ?apply_on_insn:(apply = print_insn) (_, f) =
	if Util.is_fnc_static f then Printf.printf "static ";
	let str = get_fnc_name f in
		Printf.printf "%s(" str;
		print_list var_to_string f.args;
		Printf.printf "):\n";
	match f.cfg with
		| Some bbs -> print_cfg apply bbs
		| None -> ()

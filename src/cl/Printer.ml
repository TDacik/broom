(* Pretty printer for Code Listener Storage *)

open Operand
open Var
open Fnc

let empty_output = Printf.printf ""

let error msg = Printf.eprintf "error: %s\n" msg

let get_fnc_name f =
	let op_data = f.Fnc.def.data in
	match op_data with
		| OpCst { cst_data } -> ( match cst_data with
			| CstFnc {uid; name; is_extern; loc} -> ( match name with
				| Some x -> x
				| None -> "" )
				(* Option.is_none / Option.is_some *)
			| _ -> raise Not_found )
		| _ -> raise Not_found


(* Print function's name from association list *)
let print_name_fnc fncmap uid =
	let f = List.assoc uid fncmap in
	let str = get_fnc_name f in
		Printf.printf "%s\n" str

let variable_to_string uid accs = "var"                  (* TODO: variable *)

let const_ptr_to_string ptr accs =
	let str_acc = ( match accs with
		| ac::[] -> ( match ac.acc_data with
			| Deref -> "*"
			| _ -> error "unexpected accessor by constant pointer"; "" )
		| _ -> error "too much accessors by constant pointer"; "" ) in
	if ptr==0 then "NULL" else Printf.sprintf "%s0x%x" str_acc ptr

(* Get CL constant as string *)
let constant_to_string data accs =
	match data with
	| CstPtr ptr -> const_ptr_to_string ptr accs
	| CstStruct | CstUnion | CstArray ->
		error "unsupported compound literal"; "?"
	| CstFnc {uid; name; is_extern; loc} -> ( match name with
		| Some x -> x
		| None -> error "anonymous function"; "" )
	| CstInt i -> Int64.to_string i                 (* TODO: test unsigned *)
	| CstEnum e -> Printf.sprintf "%i" e            (* TODO: test unsigned *)
	| CstChar c -> "\'" ^ Printf.sprintf "%c" c ^ "\'"
	| CstBool b -> Printf.sprintf "%B" b
	| CstReal f -> Printf.sprintf "%g" f
	| CstString str -> "\"" ^ String.escaped str ^ "\""

(* Get CL operand as string *)
let operand_to_string op =
	match op.Operand.data with
		| OpVar uid -> variable_to_string uid op.accessor
		| OpCst { cst_data } -> constant_to_string cst_data op.accessor
		| OpVoid -> "void"

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

let rec print_list_op args =
	match args with
	| [] -> ()
	| lst::[] -> let str_arg = variable_to_string lst [] in
		Printf.printf "%s" str_arg
	| hd::tl ->  let str_arg = variable_to_string hd [] in 
		Printf.printf "%s," str_arg;
		print_list_op tl

(* Print call instruction; ops = dst, called, ?args+ *)
let print_call_insn ops =
	match ops with
	| hd::snd::args ->
		let str_dst = operand_to_string hd in
		let str_called = operand_to_string snd in
			Printf.printf "\t\t%s = %s(" str_dst str_called;
			print_list_op args;
			Printf.printf ")\n"
	| _ -> error "wrong call instruction"

(* Print CL instruction *)
let print_insn insn =
	match insn.code with
	| InsnNOP -> Printf.printf "\t\tnop\n"
	| InsnJMP uid -> Printf.printf "\t\tgoto L%i\n" uid
	| InsnCOND (cond, tg_then, tg_else) -> let op = operand_to_string cond in
		Printf.printf "\t\tif (%s)\n\t\t\tgoto L%i\n\t\telse\n\t\t\tgoto L%i\n"  op tg_then tg_else
	| InsnRET ret -> let op = operand_to_string ret in
		Printf.printf "\t\tret %s\n" op
	| InsnCLOBBER var -> let op = operand_to_string var in
		Printf.printf "\t\tclobber %s\n" op
	| InsnABORT -> Printf.printf "\t\tabort\n"
	| InsnUNOP (code, dst, src) -> print_unary_insn code dst src
	| InsnBINOP (code, dst, src1, src2) -> print_binary_insn code dst src1 src2
	| InsnCALL ops -> print_call_insn ops
	| InsnSWITCH _ -> error "unsupported switch instruction"
	| InsnLABEL _ -> empty_output (* unused *)

(* Print basic block of function *)
let print_bb bb =
	Printf.printf "\tL%i:\n" bb.uid;
	List.iter print_insn bb.insns

let is_fnc_static f =
	let scope = f.Fnc.def.scope in
		scope == CL_SCOPE_STATIC

(* Print function *)
let print_fnc (uid, f) =
	if is_fnc_static f then Printf.printf "static ";
	let str = get_fnc_name f in
		Printf.printf "%s(" str;
		print_list_op f.args;
		Printf.printf "):\n";
	match f.cfg with
		| Some bbs -> List.iter print_bb bbs
		| None -> ()

(* Print variable's name from association list *)
let print_name_var vmap uid = 
	let v = List.assoc uid vmap in
	( match v.Var.name with
		| Some x -> Printf.printf "%s\n" x
		| None -> Printf.printf "\n" )

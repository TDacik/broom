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

(* Pretty printer for Code Listener Storage *)

open Operand
open Var
open Fnc

(* TODO: use exceptions *)


let empty_output = ()



(* TODO type *)
let type_to_string _ (* uid *) = ""

let var_to_string uid =
	let v = Util.get_var uid in
	let uid_str = string_of_int uid in
	let scope = (match v.code with
		| VAR_GL -> "S"
		| VAR_LC | VAR_FNC_ARG -> "F"
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

(* Return chained item accessors with corresponding offset
   e.g. (".next.prev", 8, rest of accessors) for '[+8].next.prev' *)
and item_accessors accs =
	match accs with
	| [] -> ("", 0, accs)
	| ac::tl -> (match ac.acc_data with
		| Item _ ->
			let (item_name, ioff, _) = Util.get_accessor_item ac in
			let (rest, off, rest_tl) = item_accessors tl in
			let new_off = off + ioff in
			("." ^ item_name ^ rest, new_off, rest_tl)
		| _ -> ("", 0, accs) )

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
		| Item _ (* num *) ->
			let (names, off, rest_tl) = item_accessors accs in
			let rest = back_accessors rest_tl in
			let off_str = string_of_int off in
			"[+" ^ off_str ^ "]" ^ names ^ rest
		| Offset off -> let rest = back_accessors tl
			and id_str = string_of_int off
			and sign = (if off >= 0 then "+" else "") in
			".<" ^ sign ^ id_str ^ ">" ^ rest
		| Ref -> Msg.internal ("invalid reference accessor",__POS__); ""
		| _ -> Msg.internal ("unsupported accessor",__POS__); "")

and middle_var uid accs =
	let var = var_to_string uid in
	let rest = back_accessors accs in
		var ^ rest

and front_accessors uid accs =
	match accs with
	| [] -> middle_var uid []
	| ac::tl -> ( match ac.acc_data with
		| Deref -> let rest = front_accessors uid tl in "*" ^ rest
		| _ -> middle_var uid (ac::tl) )

and op_var_to_string uid accs =
	if (accs != []) then ( (* last accessor could be reference *)
		let rev_accs = List.rev accs in
		let ac = List.hd rev_accs in
		match ac.acc_data with
			| Ref -> "&" ^ (front_accessors uid (List.rev (List.tl rev_accs)))
			| _ -> front_accessors uid accs)
	else
		middle_var uid accs

and const_ptr_to_string ptr accs =
	let str_acc = ( match accs with
		| [] -> ""
		| ac::[] -> ( match ac.acc_data with
			| Deref -> "*"
			| _ -> Msg.internal ("unexpected accessor by constant pointer",__POS__); "" )
		| _ -> Msg.internal ("too much accessors by constant pointer",__POS__); "" ) in
	if ptr==0 then "NULL" else Printf.sprintf "%s0x%x" str_acc ptr

and constant_to_string data accs =
	match data with
	| CstPtr ptr -> const_ptr_to_string ptr accs
	| CstStruct | CstUnion | CstArray ->
		Msg.internal ("unsupported compound literal",__POS__); "?"
	| CstFnc fnc -> ( match fnc.name with
		| Some x -> x
		| None -> Msg.internal ("anonymous function",__POS__); "" )
	| CstInt i -> Int64.to_string i                 (* TODO: test unsigned *)
	| CstEnum e -> Printf.sprintf "%i" e            (* TODO: test unsigned *)
	| CstChar c -> "\'" ^ Printf.sprintf "%c" c ^ "\'"
	| CstBool b -> Printf.sprintf "%B" b
	| CstReal f -> Printf.sprintf "%g" f
	| CstString str -> "\"" ^ String.escaped str ^ "\""



let get_fnc_name f = operand_to_string f.Fnc.def

let fnc_declaration_to_string f =
	let str_static = (if Util.is_fnc_static f then "static " else "") in
	let str_args = Util.list_to_string var_to_string f.args in
	str_static ^ (get_fnc_name f) ^ "(" ^ str_args ^ ")"

(* Get unary CL instruction as string *)
let unary_insn_to_string code dst src =
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
	str_dst^" := "^unop^str_src^e

(* Get binary CL instruction as string *)
let binary_insn_to_string code dst src1 src2 =
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
		| CL_BINOP_POINTER_MINUS -> "[ptr]-"
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
	str_dst^" := ("^str_src1^" "^binop^" "^str_src2^")"

(* Get call instruction; ops = dst, called, ?args+ as string *)
let call_insn_to_string ops =
	match ops with
	| hd::snd::args ->
		let str_called = operand_to_string snd in
		let str_dst = (if not (Util.is_void hd)
			then operand_to_string hd ^ " := "
			else "") in
		let str_args = Util.list_to_string operand_to_string args in
		str_dst^str_called^"("^str_args^")"
	| _ -> Msg.internal ("wrong call instruction",__POS__); ""

let cond_insn_to_string ?indent:(indent=false) cond tg_then tg_else =
	let (beg,goto,els) = (if (indent)
		then "\t\t","\n\t\t\t","\n\t\t"
		else ""," "," ") in
	beg^"if ("^(operand_to_string cond)^")"^
	goto^"goto L"^(string_of_int tg_then)^
	els^"else"^
	goto^"goto L"^(string_of_int tg_else)

let insn_to_string ?indent:(indent=false) insn =
	let ind = (if (indent) then "\t\t" else "") in
	match insn.code with
	| InsnNOP -> ind ^ "nop"
	| InsnJMP uid -> ind ^ "goto L" ^ (string_of_int uid)
	| InsnCOND (cond, tg_then, tg_else) ->
		cond_insn_to_string ~indent:indent cond tg_then tg_else
	| InsnRET ret -> let op = (if not (Util.is_void ret)
			then " " ^ operand_to_string ret
			else "") in
		ind ^ "return" ^ op
	| InsnCLOBBER var ->
		ind ^ "clobber " ^ (operand_to_string var)
	| InsnABORT -> ind ^ "abort"
	| InsnUNOP (code, dst, src) ->
		ind ^ (unary_insn_to_string code dst src)
	| InsnBINOP (code, dst, src1, src2) ->
		ind ^ (binary_insn_to_string code dst src1 src2)
	| InsnCALL ops -> ind ^ (call_insn_to_string ops)
	| InsnSWITCH _ -> Msg.internal ("unsupported switch instruction",__POS__); ""
	| InsnLABEL _ -> "" (* unused *)

(* Print CL instruction *)
let print_insn insn =
	let str_insn = insn_to_string ~indent:true insn in
	if (str_insn = "") then ()
	else print_endline str_insn

let prerr_insn insn =
	let str_insn = insn_to_string ~indent:true insn in
	if (str_insn = "") then ()
	else prerr_endline str_insn

let print_block apply_on (uid, bb) =
	print_endline ("\tL" ^ (string_of_int uid) ^ ":");
	List.iter apply_on bb.insns

let rec print_cfg apply_on_insn cfg =
	match cfg with
	| [] -> ()
	| bb::tl -> print_block apply_on_insn bb; print_cfg apply_on_insn tl

(* Print function *)
let print_fnc ?apply_on_insn:(apply = print_insn) (_, f) =
	print_endline ((fnc_declaration_to_string f)^":");
	print_cfg apply f.cfg

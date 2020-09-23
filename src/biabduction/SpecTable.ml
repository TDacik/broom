type cl_uid = CL.Loc.cl_uid

type status = OK | Error | Aborted (* | Unreached *)

(*
  key is a unique uid of function
  value is list of contracts (pre, post1), (pre, post2)
        // or (pre, [post1,post2])... ?
*)

type t = (cl_uid, (Contract.t * status) list) Hashtbl.t

let create = let (fnc_tbl : t) = Hashtbl.create 1 in fnc_tbl

(* TODO change value to mutable? *)
let add tbl uid specs =
	let found = Hashtbl.find_opt tbl uid in
	match found with
	| None -> Hashtbl.add tbl uid specs
	| Some s -> Hashtbl.replace tbl uid (s @ specs) (* TODO join *)

let find_opt tbl x = Hashtbl.find_opt tbl x

let status_to_string s =
	match s with
	| OK -> ""
	| Error -> "[error]"
	| Aborted -> "[aborted]"

let spec_to_string (contract,s) =
	(status_to_string s) ^ (Contract.to_string contract)

(** printing on standard output *)

let print_spec uid specs =
	let fnc_decl = CL.Printer.fnc_declaration_to_string (CL.Util.get_fnc uid) in
	print_endline (">>> spec of function " ^ fnc_decl ^ ":");
	CL.Util.print_list_endline spec_to_string specs

let print tbl =
	print_endline ("FUNCTIONS: " ^ (Int.to_string (Hashtbl.length tbl)));
	Hashtbl.iter print_spec tbl

let reset = Hashtbl.reset

type cl_uid = CL.Loc.cl_uid

(*
  key is a unique uid of function
  value is list of contracts (pre, post1), (pre, post2)
        // or (pre, [post1,post2])... ?
*)

type t = (cl_uid, Contract.t list) Hashtbl.t

let create = let (fnc_tbl : t) = Hashtbl.create 1 in fnc_tbl

(* TODO change value to mutable? *)
let add tbl uid contracts =
	let found = Hashtbl.find_opt tbl uid in
	match found with
	| None -> Hashtbl.add tbl uid contracts
	| Some c -> Hashtbl.replace tbl uid (c @ contracts) (* TODO join *)

let find_opt tbl x = Hashtbl.find_opt tbl x

let print_spec uid contracts =
	print_string ">>> spec of function ";
	CL.Printer.print_fnc_declaration (CL.Util.get_fnc uid);
	print_endline ":";
	CL.Util.print_list Contract.to_string contracts;
	print_newline ()

let print tbl =
	print_endline ("FUNCTIONS: " ^ (Int.to_string (Hashtbl.length tbl)));
	Hashtbl.iter print_spec tbl

let reset = Hashtbl.reset

type variable = int (* uid *) 

let compare_variable x y = compare

module Expr = struct
    type t = 
      | Var of variable
      | Const of const_val
      (* todo | Interval... *)
      | UnOp of unop * t
      | BinOp of binop * t * t 
      | Void
      | Undef
    
    and unop = [ `Base | `Len | `Size | `Freed ] 

    (* aritmetic operation *)
    and binop = [
      | `Peq    (** equality *)
      | `Pneq   (** nonequality *)
      | `Pless  (** less then *) 
      | `Pplus
      | `Pminus (** in same alloc block *) ]

    and const_val = [
        `Ptr of int
      | `Int of int
      | `Bool of int
      | `String of string
      | `Float of float ]
   

    (*let equal = [%compare.equal: t]*)
end

(* pure part *)
type pi = Expr.t list

type heap_pred =
  | Hpointsto of Expr.t * Expr.t (* bez off -> v pi / mozno interval a ine *)
  (* todo *)

(* spatial part *)
type sigma = heap_pred list

(* substitution map *)
(** Param for vars from params of function and global vars. *)
type kind = KReg | KProg | KLogic | KParam [@@deriving compare]

type name = (kind * variable)

(* let equal_kind = [%compare.equal: kind]*)

(* all variables  
module Set = Caml.Set.Make (struct
  type t = name
  let compare = compare
end)*)

(* map from logic vars --> to program vars [registers and memory] 
module Map = Caml.Map.Make (struct
  type t = int
  let compare = compare
end)*)

(*
module Foo = struct
   module T = struct
     type t = name
     let compare x y = Tuple2.compare compare_kind compare_variable
     let sexp_of_t = Tuple2.sexp_of_t Int.sexp_of_t Int.sexp_of_t
   end
   include T
   include Comparable.Make(T)
end *)


(* let get_pvar_from_lvar luid = *)

(* List.exists - test emptiness *)

(** formula *)
type t = { 
    sigma: sigma;  (** spatial part *)
    pi: pi;  (** pure part *)
(*    sub: Map.t; * map : log_var id --> prog_var uid *)
(*    evars: Set.t; ** existential variables *)
}


let rec find_target xx fs =
(*	let Hpointsto (xx, _) = p in *)
		match fs with
		| [] -> None
		| Hpointsto (x, y) :: t -> if xx = x then Some y else find_target xx t



let form1 = {
    sigma = [ Hpointsto (Var 1, Var 2) ];
    pi = [ BinOp ( `Peq, Var 1, UnOp ( `Base, Var 1));
          BinOp ( `Peq, UnOp ( `Len, Var 1), Const (`Int 8));
      (*  BinOp ( `Peq, Var 1, BinOp ( `Pplus, Var 2332, Const (`Int 0) ) ); *)
          BinOp ( `Peq, Var 1, Var 2332 );
          BinOp ( `Peq, UnOp ( `Size, Var 1), Const (`Int 4));
          BinOp ( `Peq, Var 2, Const (`Ptr 0)) ]
}

let pre_free = {
    sigma = [ Hpointsto (Var 2332, Undef) ];
    pi = [ BinOp ( `Peq, Var 2332, UnOp ( `Base, Var 2332)) ]
}

let post_free = {
    sigma = [];
    pi = [ BinOp ( `Peq, Var 2332, UnOp ( `Base, Var 2332)); UnOp ( `Freed, Var 2332) ]
}

(* find all var = var in pure part and return map (progvar, logvar) *)
(* find equation in pure part pi for all program variables *)
let rec get_varmap f =
	match f with
	| [] -> []
	| elm :: t -> ( match elm with
		| Expr.BinOp ( `Peq, Var fst, Var scd) -> ( fst, scd ) :: get_varmap t 
		                                        (* odlisit prog od log vars *)
		| _ -> get_varmap t)

(* get all variables equivalent with v in assoc list map *)
let rec get_eq_vars v map =
	match map with
	| [] -> []
	| (v1, v) :: t -> v1 :: get_eq_vars v t
	| (v, v2) :: t -> v2 :: get_eq_vars v t
	| _ :: t -> get_eq_vars v t

let rec find_target_from_list xxs fs =
	(match xxs with
	| [] -> raise Not_found
	| xx :: t -> let tg = find_target (Var xx) fs in
					(match tg with
					| None -> find_target_from_list t fs
					| Some y -> y)
	)

let get_eq_vars x f1 f2 =  
	let varmap1 = get_varmap f1.pi in (* only prog variables *)
		let xlist1 = get_eq_vars x varmap1 in
			let varmap2 = get_varmap f2.pi in
				let xlist2 = get_eq_vars x varmap2 in (* nad vsetkymi xlist? bude ich viac? *)
					List.append (x :: xlist1) xlist2

(* first hpread from formula try to find in formula *)
let rec match1_get_target pre act = 
	match pre.sigma with
		| [] -> raise Not_found
		| Hpointsto (Var xx, _) :: t -> let xxs = get_eq_vars xx pre act in 
			find_target_from_list xxs act.sigma
		


type variable = int

(* NOTE: original name Expr was renamed to Exp due to name collision with Z3.Expr *)
module Exp = struct
    type t = 
      | Var of variable
      | Const of const_val
      (* todo | Interval... *)
      | UnOp of unop * t
      | BinOp of binop * t * t 
      | Void
      | Undef
    
    and unop =  Base | Len | Size | Freed  

    (* aritmetic operation *)
    and binop = 
      | Peq    (** equality *)
      | Pneq   (** nonequality *)
      | Pless  (** less then *) 
      | Plesseq (** less or equal then **)
      | Pplus
      | Pminus (** in same alloc block *) 

    and const_val = 
        Ptr of int
      | Int of int
      | Bool of bool
      | String of string
      | Float of float 
   
let const_to_string c=
	match c with
	| Ptr a -> ">" ^ string_of_int a
	| Int a -> string_of_int a
	| Bool a -> "B" ^  string_of_bool a
	| String a -> a
	| Float a ->  string_of_float a

let unop_to_string o =
	match o with
	| Base -> "base"
	| Len -> "len"
	| Size -> "size"
	| Freed -> "freed"

let binop_to_string o =
	match o with
	| Peq ->  "="
	| Pneq -> "!="
	| Pless -> "<" 
	| Plesseq -> "<=" 
      	| Pplus -> "+"
      	| Pminus -> "-" 



let rec to_string e =
    match e with
    | Var a -> "V" ^ string_of_int a
    | Const a -> const_to_string a
    | UnOp (op,a) -> unop_to_string op ^ "(" ^ to_string a ^ ")"
    | BinOp (op,a,b) -> "(" ^ to_string a ^ binop_to_string op ^  to_string b ^ ")"
    | Void -> "Void"
    | Undef -> "Undef"

end

(* pure part *)
type pi = Exp.t list

type heap_pred =
  | Hpointsto of Exp.t * Exp.t (* bez off -> v pi / mozno interval a ine *)
  (* todo *)

(* spatial part *)
type sigma = heap_pred list

let rec sigma_to_string s =
	let pred_to_list a =
		match a with
		| Hpointsto (a,b) -> Exp.to_string a ^ " -> " ^ Exp.to_string b
	in
	match s with 
	| [] -> ""
	| first::rest -> pred_to_list first ^ " * " ^ sigma_to_string rest

(** formula *)
type t = { 
    sigma: sigma;  (** spatial part *)
    pi: pi;  (** pure part *)
}

let to_string f =
	let rec evars_to_string ev =
		match ev with
		|[] -> ""
		| first::rest -> "V" ^ string_of_int first ^ ", " ^ evars_to_string rest
	in	
	let rec pi_to_string p =
		match p with 
		| [] -> ""
		| first::rest -> Exp.to_string first ^ " & " ^  pi_to_string rest
	in
	(*"[Ex. " ^ evars_to_string f.evars ^ "] " ^*)
	sigma_to_string f.sigma ^ pi_to_string f.pi


(*** FIND ALL VARIABLES IN FORMULA ***)
(* add missing elements of list l1 to l2 *)
let rec join_list_unique l1 l2 =
	let mem x =
		let eq y= (x=y) in
		List.exists eq l2
	in
	match l1 with
	| [] -> l2
	| first::rest ->
		if mem first 
		then join_list_unique rest l2 
		else join_list_unique rest (first::l2)


let rec find_vars_expr expr =
	match expr with 
     	| Exp.Var a -> [a] 		
      	| Const a -> []
      	| UnOp (op,a) -> find_vars_expr a
      	| BinOp (op,a,b) -> List.append (find_vars_expr a) (find_vars_expr b)
      	| Void -> []
      	| Undef -> []

let rec find_vars_pi pi =
	match pi with
	| [] -> []
	|first::rest -> 
		join_list_unique (find_vars_expr first) ( find_vars_pi rest)

let rec fin_vars_sigma sigma = 
	match sigma with
	| [] -> []
	| Hpointsto (a, b)::rest ->
		join_list_unique (find_vars_expr a)
		(join_list_unique (find_vars_expr b) (fin_vars_sigma rest))

(* This function provides a list of all variables used in the formula form *)
let find_vars form =
	join_list_unique (fin_vars_sigma form.sigma) (find_vars_pi form.pi)

(**** FORMULA SIMPLIFICATION ****)
(* Function to simplify formula by removing equivalent existential variables *)
(* get a list of pair of equal variables from Pure part *)
let rec get_varmap f =
	match f with
	| [] -> []
	| elm :: t -> ( match elm with
		| Exp.BinOp ( Peq, Var fst, Var scd) -> ( fst, scd ) :: get_varmap t 
		| _ -> get_varmap t)

(* get all variables equivalent with variables in list "vlist" *)
let rec get_eq_vars_ll vlist equalities =
	let mem x =
		let eq y= (x=y) in
		List.exists eq vlist
	in
	match equalities with
	| [] -> []
	| (a,b) :: rest ->
		let add_1 = if ((mem a) && (not (mem b) )) then [b] else [] in
		let add_2 = if ((mem b) && (not (mem a) )) then [a] else [] in
		List.append add_2 (List.append add_1 (get_eq_vars_ll vlist rest))

(* We are computing a transitive closure *)
let rec get_eq_vars vlist equalities =
	let eq = get_eq_vars_ll vlist equalities in
	match eq with 
	| [] -> []
	| _ -> join_list_unique eq (get_eq_vars (join_list_unique eq vlist) equalities)


let rec substitute_sigma var1 var2 sigma =
	match sigma with
		| [] -> []
		| Hpointsto (a, b) ::rest ->
			let a_new = match (a=Exp.Var var2) with 
				| true -> Exp.Var var1
				| false -> a
			in
			let b_new = match (b=Exp.Var var2) with
				| true -> Exp.Var var1
				| false -> b
			in
			Hpointsto (a_new,b_new) :: substitute_sigma var1 var2 rest

let rec substitute_expr var1 var2 expr =
	match expr with 
     	| Exp.Var a ->
		if (a=var2) 
		then Exp.Var var1
		else Exp.Var a
      	| Const a -> Const a
      	| UnOp (op,a) -> UnOp (op, substitute_expr var1 var2 a)
      	| BinOp (op,a,b) -> BinOp (op, substitute_expr var1 var2 a, substitute_expr var1 var2 b)
      	| Void -> Void
      	| Undef -> Undef

let rec substitute_pi var1 var2 pi =
	match pi with
	| expr::rest -> (substitute_expr var1 var2 expr) :: (substitute_pi var1 var2 rest)
	|  [] -> []


let substitutevars var1 var2 form = 
	let sigma_out = substitute_sigma var1 var2 form.sigma in
	let pi_out=substitute_pi var1 var2 form.pi in
	{sigma = sigma_out; pi = pi_out} 
	(*{sigma = sigma_out; pi = pi_out; evars = form.evars} *)

let rec substitute var1 eqvarlist form = 
	match eqvarlist with
	| [] -> form
	| first::rest ->
		let form1=substitutevars var1 first form in
			substitute var1 rest form1


(* simplify the formula,
   gvars - global variables, evars - existential variables *)
let rec simplify_ll gvars evars form = 
	let equiv=get_varmap form.pi in
	match gvars with
	| [] -> form
	| a :: rest -> 	
		let eq_vars=(get_eq_vars [a] equiv) in
		let mem x =
			let eq y= (x=y) in
			List.exists eq evars
		in
		let eq_vars_ex = List.filter mem eq_vars in
		let form1= substitute a eq_vars_ex form in
			simplify_ll rest evars form1


(* remove redundant equalities from pure part formula *)
let rec remove_redundant_eq pi =
	match pi with
	| [] -> []
	| first::rest ->
		match first with
		| Exp.BinOp (Peq,a,b) -> if a=b 
			then remove_redundant_eq rest
			else Exp.BinOp (Peq,a,b) :: (remove_redundant_eq rest)
		| x -> x:: (remove_redundant_eq rest)

let rec remove_unused_evars_ll evars vars =
	let mem x =
		let eq y= (x=y) in
		List.exists eq vars
	in
	match evars with
	| [] -> []
	| first::rest -> if mem first
			then first::(remove_unused_evars_ll rest vars)
			else (remove_unused_evars_ll rest vars)

let remove_unused_evars form evars =
	let vars=find_vars form in
	remove_unused_evars_ll evars vars


(* now we have everything for global simplify function,
   evars is a list of Ex. q. variables, which can be renamed/removed/etc...*)
let simplify form evars=
	let mem x =
		let eq y= (x=y) in
		not (List.exists eq evars )
	in
	let vars=find_vars form in
	let gvars=List.filter mem vars in
	let form1 = simplify_ll gvars evars form in
	{ sigma=form1.sigma; 
	  pi=remove_redundant_eq form1.pi }
	(*let form2 = { 
		sigma=form1.sigma;
		pi=remove_redundant_eq form1.pi;
		evars = form1.evars
	} in
	remove_unused_evars form2*)

	
(*** RENAME CONFLICTING LOGICAL VARIABLES ***)
(* The existentially quantified variables are renamed to avoid conflicts 
  in other formulas *)

let rec rename_ex_variables_ll form all_vars to_rename conflicts seed new_evars=
	let mem x l =
		let eq y= (x=y) in
		List.exists eq l
	in
	let rec get_fresh_var s confl=
		if (mem s confl)
		then get_fresh_var (s+1) confl
		else s
	in
	match to_rename with
	| [] -> { sigma = form.sigma; pi= form.pi}, new_evars
	| first::rest -> if (mem first conflicts)
			then 
				let new_var = get_fresh_var seed (List.append all_vars conflicts) in
				let new_form = substitutevars new_var first form in
				rename_ex_variables_ll new_form all_vars rest conflicts (new_var+1) (new_var :: new_evars)
			else rename_ex_variables_ll form all_vars rest conflicts seed (first :: new_evars)


(* create fresh names for evars with conflicts *)
let rename_ex_variables form evars conflicts =
	let all_vars = find_vars form in
	rename_ex_variables_ll form all_vars evars conflicts 1 []




(******** EXPERIMENTS *******)

let form1 = {
    sigma = [ Hpointsto (Var 1, Var 2) ];
    pi = [ BinOp ( Peq, Var 1, UnOp ( Base, Var 1));
          BinOp ( Peq, UnOp ( Len, Var 1), Const (Int 8));
          BinOp ( Peq, Var 1, Var 2332 );
          BinOp ( Peq, UnOp ( Size, Var 1), Const (Int 4));
          BinOp ( Peq, Var 2, Const (Ptr 0)) ]
    (*evars = [ 2 ]*)
}

(*List.map (Expr.to_string) form1.pi;;*)

(*to_string form1*)

let pre_free = {
    sigma = [ Hpointsto (Var 2332, Undef) ];
    pi = [ BinOp ( Peq, Var 2332, UnOp ( Base, Var 2332)) ]
    (*evars = []*)
}

let post_free = {
    sigma = [];
    pi = [ BinOp ( Peq, Var 2332, UnOp ( Base, Var 2332)); UnOp ( Freed, Var 2332) ];
    (* evars = [] *)
}

let form2 = {
    sigma = [ Hpointsto (Var 1, Var 2); Hpointsto(Var 3, Var 4) ];
    pi = [ BinOp ( Peq, Var 1, UnOp ( Base, Var 1));
    	  BinOp ( Peq, Var 1, UnOp ( Base, Var 3));
          BinOp ( Peq, UnOp ( Len, Var 1), Const (Int 8));
          BinOp ( Peq, Var 1, Var 2332 );
          BinOp ( Peq, Var 2, Const (Ptr 0)) ]
    (*evars = [ 2;3;4 ]*)
}

let form3 = {
    sigma = [ Hpointsto (Var 1, Var 2); Hpointsto(Var 3, Var 4) ];
    pi = [ BinOp ( Peq, Var 1, UnOp ( Base, Var 1));
          BinOp ( Peq, UnOp ( Len, Var 1), Const (Int 8));
          BinOp ( Peq, Var 1, Var 2332 );
          BinOp ( Peq, Var 2, Const (Ptr 0)) ]
    (*evars = [ 2;3;4 ]*)
}



(* in utop type: 
   #mod_use "Formula.ml" and then you can do e.g. Formula.simplify Formula.form1 
   #load "Formula.cmo" to load compiled version
   open Formula and then you can do e.g. simplify form1 *)



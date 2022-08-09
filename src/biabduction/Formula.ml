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

(* NOTE: original name Expr was renamed to Exp due to name collision with Z3.Expr *)
module Exp = struct (*$< Exp *)
    type t =
        Var of variable (** lvars - existential local variables in the scope of
                                    a function
                                  - spetial cases: var 0 - return, var uid<0
                                    anchors
                            pvars - program variables, unique in the scope of
                                    a file *)
      | CVar of int
      | Const of const_val
      (* todo | Interval... *)
      | UnOp of unop * t
      | BinOp of binop * t * t
      | Void
      | Undef

    and unop =
        Base
      | Len
      | Stack    (** stack allocation *)
      | Static   (** static storage *)
      | Freed    (** for heap allocation *)
      | Invalid  (** for stack allocation *)
      | BVnot    (** bitwise, in C: ~ *)
      | Pnot     (** logical, in C: ! *)
      | Puminus  (** in C: - *)

    (* aritmetic operation *)
    and binop =
      | Peq      (** equality *)
      | Pneq     (** nonequality *)
      | Pless    (** less then *)
      | Plesseq  (** less or equal then *)
      | Pand     (** logical AND *)
      | Por      (** logical OR *)
      | Pxor     (** logical XOR *)
      | Pplus
      | Pminus   (** for pointers - in same alloc block *)
      | Pmult
      | Pdiv     (** CL_BINOP_EXACT_DIV: for pointers - div without rounding *)
      | Pmod
      | BVand    (** bitwise AND *)
      | BVor     (** bitwise OR *)
      | BVxor    (** bitwise XOR *)
      | BVlshift
      | BVrshift (** logical on unsigned, arithmetic on signed *)
      | BVlrotate
      | BVrrotate

    and const_val =
        Ptr of int
      | Int of Int64.t
      | Bool of bool
      | String of string
      | Float of float

    and variable = int

let one = Const (Int 1L)
let zero = Const (Int 0L)
let null = Const (Ptr 0) (* TODO: need Ptr ? *)
let ret = Var 0

let rec variable_to_string ?lvars:(lvars=[]) v =
  let var = if (lvars <> [] && List.mem v lvars)
    then None
    else CL.Util.get_var_opt v in
  match var with
  | None when v=0 -> "%ret" (* special var for return value *)
  | None when v<0 ->
    (variable_to_string (-v))^"_anch" (* special var from program var *)
  | None -> "%l" ^ string_of_int v
  | Some _ -> CL.Printer.var_to_string v

let lvariable_to_string v = variable_to_string ~lvars:[v] v

let cvariable_to_string v = "%c" ^ string_of_int v

let const_to_string c =
  match c with
  | Ptr a -> if a==0 then "NULL" else Printf.sprintf "0x%x" a
  | Int a -> Int64.to_string a
  | Bool a -> string_of_bool a
  | String a -> "\"" ^ String.escaped a ^ "\""
  | Float a ->  string_of_float a

let unop_to_string o =
  match o with
  | Base -> "base"
  | Len -> "len"
  | Stack -> "stack"
  | Static -> "static"
  | Freed -> "freed"
  | Invalid -> "invalid"
  | BVnot -> "~"
  | Pnot -> "!"
  | Puminus -> "-"

let binop_to_string o =
  match o with
  | Peq ->  "="
  | Pneq -> "!="
  | Pless -> "<"
  | Plesseq -> "<="
  | Pand -> "&&"
  | Por -> "||"
  | Pxor -> "xor"
  | Pplus -> "+"
  | Pminus -> "-"
  | Pmult -> "*"
  | Pdiv -> "/"
  | Pmod -> "%"
  | BVand -> "&"
  | BVor -> "|"
  | BVxor -> "^"
  | BVlshift -> "<<"
  | BVrshift -> ">>"
  | BVlrotate -> "lrotate"
  | BVrrotate -> "rrotate"

let rec to_string ?lvars:(lvars=[]) e =
  match e with
  | Var a -> variable_to_string ~lvars:lvars a
  | CVar a -> cvariable_to_string a
  | Const a -> const_to_string a
  | UnOp (op,a) -> unop_to_string op ^ "(" ^ to_string ~lvars:lvars a ^ ")"
  | BinOp (op,a,b) ->
    "(" ^ to_string ~lvars:lvars a ^ binop_to_string op ^
    to_string ~lvars:lvars b ^ ")"
  | Void -> "Void"
  | Undef -> "Undef"

let get_list_vars uids =
  let constr v =
    Var v
  in
  List.map constr uids

let get_list_uids vars =
  let unpack v =
    match v with
    | Var a -> Some a
    | _ -> None
  in
  List.filter_map unpack vars

end (*$>*)

exception ErrorInFormula of (string * Config.src_pos)

(************************************************************
  type definition of Formula
 ************************************************************)
(** formula *)
type t = {
    sigma: sigma;  (** spatial part *)
    pi: pi;  (** pure part *)
}

(* pure part *)
and pi = Exp.t list

(* lambda *)
and lambda = {
  param: Exp.variable list;
  form: t;
}

and heap_pred =
  | Hpointsto of Exp.t * Exp.t * Exp.t (* source, size_of_field, destination *)
  (* We use type 'Exp.t list' for shared nodes because this allows us to handle arithmetic 
    compositions on pointers *)
  | Slseg of Exp.t * Exp.t * lambda * Exp.t list   (* source, destination, lambda, shared *) 
  (* first, backlink from first, last, forwardlink from last, lambda, shared *)
  | Dlseg of Exp.t * Exp.t * Exp.t * Exp.t * lambda * Exp.t list

(* spatial part *)
and sigma = heap_pred list

let empty = {sigma = []; pi = []}

(* PRINTING *)

let lvariables_to_string lvars =
  CL.Util.list_to_string (Exp.variable_to_string ~lvars:lvars) lvars

let rec pi_to_string ?lvars:(lvars=[]) p =
  match p with
  | [] -> ""
  | first::[] -> Exp.to_string ~lvars:lvars first
  | first::rest -> Exp.to_string ~lvars:lvars first ^ " & " ^
    pi_to_string ~lvars:lvars rest

let points_to_to_string ?lvars:(lvars=[]) points_to = 
  match points_to with
  | Hpointsto(a,l,b) ->
  Exp.to_string ~lvars:lvars a ^" -("^
      (Exp.to_string ~lvars:lvars l) ^")->"^
      Exp.to_string ~lvars:lvars b
  | _ -> ""    

let rec sigma_to_string_ll ?lvars:(lvars=[]) s lambda_level num=
(* num is used to marking lambdas *)
  let rec lambda_params_to_string params =
    match params with
    | [] -> ""
    | first::rest -> (Exp.lvariable_to_string first)^", "^
      (lambda_params_to_string rest)
  in
  let pred_to_string a =
    match a with
    | Hpointsto (a,l,b) -> points_to_to_string (Hpointsto (a,l,b)), ""
    | Slseg (a,b,lambda,shared) ->
      let lambda_id= "lambda-"^(string_of_int lambda_level)^":"^(string_of_int num) in
      ("Slseg(" ^ Exp.to_string ~lvars:lvars a ^", "^
        Exp.to_string ~lvars:lvars b ^", "^
        lambda_id^ ", ["^ String.concat ", " (List.map Exp.to_string shared) ^"]) "),
      "\n"^lambda_id^" ["^(lambda_params_to_string lambda.param)^"] = "^
        (to_string_with_lambda ~lvars:lvars lambda.form  (lambda_level+1))
    | Dlseg (a,b,c,d,lambda,shared) ->
      let lambda_id= "lambda-"^(string_of_int lambda_level)^":"^(string_of_int num) in
      ("Dlseg(" ^ Exp.to_string ~lvars:lvars a ^", "^
        Exp.to_string ~lvars:lvars b ^", "^
	Exp.to_string ~lvars:lvars c ^", "^
	Exp.to_string ~lvars:lvars d ^", "^
        lambda_id^", ["^ String.concat ", " (List.map Exp.to_string shared) ^"]) "),
      "\n"^lambda_id^" ["^(lambda_params_to_string lambda.param)^"] = "^
        (to_string_with_lambda ~lvars:lvars lambda.form  (lambda_level+1))
  in
  match s with
  | [] -> "",""
  | first::rest ->
    match (pred_to_string first),
           (sigma_to_string_ll ~lvars:lvars rest lambda_level (num+1)) with
    | (pred_first, lambda_first), ("", lambda_rest) ->
      pred_first, (lambda_first ^ lambda_rest)
    | (pred_first, lambda_first), (pred_rest, lambda_rest) ->
      (pred_first ^ " * " ^ pred_rest), (lambda_first ^ lambda_rest)

and sigma_to_string ?lvars:(lvars=[]) s lambda_level =
  sigma_to_string_ll ~lvars:lvars s lambda_level 1

(* call this function with:
   lambda_level=1 -> include translation of lambdas
   lambda_level=0 -> no translation of lambdas
*)
and to_string_with_lambda ?lvars:(lvars=[]) f lambda_level =
  match (sigma_to_string ~lvars:lvars f.sigma lambda_level),
         lambda_level,
         (pi_to_string ~lvars:lvars f.pi) with
  | ("",""), _, "" -> ""
  | ("",""), _, pi -> pi
  | (sigma, _), 0, "" -> sigma
  | (sigma, lambda_descr), _, "" -> sigma ^ "\n---------------" ^ lambda_descr
  | (sigma, _), 0, pi -> sigma ^ " & " ^ pi
  | (sigma, lambda_descr), _, pi -> sigma ^ " & " ^ pi ^ "\n---------------" ^ lambda_descr

let to_string ?lvars:(lvars=[]) f = to_string_with_lambda ~lvars:lvars f 0

let print_with_lambda ?lvars:(lvars=[]) f =
  print_endline (to_string_with_lambda ~lvars:lvars f 1)

let print ?lvars:(lvars=[]) f =
  print_endline (to_string_with_lambda ~lvars:lvars f 0)

let diff {pi = pi1; sigma = sigma1} {pi = pi2; sigma = sigma2} =
  {pi = CL.Util.list_diff pi1 pi2;
  sigma = CL.Util.list_diff sigma1 sigma2}

let disjoint_union {pi = pi1; sigma = sigma1} {pi = pi2; sigma = sigma2} =
  {pi = pi1 @ pi2;
  sigma = sigma1 @ sigma2}

let rec is_invalid pi =
  match pi with
  | [] -> false
  | Exp.UnOp (Invalid,_)::_ -> true
  | _::tl -> is_invalid tl

let rec is_sigma_abstract sigma =
  match sigma with
  | [] -> false
  | Slseg (_,_,_,_)::_ -> true
  | Dlseg (_,_,_,_,_,_)::_ -> true
  | _::tl -> is_sigma_abstract tl

let is_abstract f = is_sigma_abstract f.sigma

(*** FIND ALL VARIABLES IN FORMULA ***)

(* returns: ptr new_sigma new_cvars *)
let rec find_and_remove_var_pointsto obj sigma cvars =
  match sigma with
  | [] -> let cvar_last = cvars + 1 in
    (Exp.CVar cvar_last), [], cvar_last
  | Hpointsto (ptr,size,obj2)::rest when obj2=obj -> (
    match ptr with
    | Var _ | CVar _ -> (ptr, rest, cvars)
    | _ ->
      let (ptr0,sig0,cvars0) = find_and_remove_var_pointsto obj rest cvars in
      ptr0, Hpointsto (ptr,size,obj)::sig0, cvars0 )
  | exp::rest ->
    let (ptr0,sig0,cvars0) = find_and_remove_var_pointsto obj rest cvars in
    ptr0, exp::sig0, cvars0

(* except contract variables *)
let rec find_vars_expr expr =
  match expr with
  | Exp.Var a -> [a]
  | UnOp (_,a) -> find_vars_expr a
  | BinOp (_,a,b) -> List.append (find_vars_expr a) (find_vars_expr b)
  | CVar _ | Const _ | Void | Undef -> []

let rec find_vars_pi pi =
  match pi with
  | [] -> []
  | first::rest ->
    CL.Util.list_join_unique (find_vars_expr first) ( find_vars_pi rest)

let rec find_vars_sigma sigma =
  match sigma with
  | [] -> []
  | Hpointsto (a,_, b)::rest ->
    CL.Util.list_join_unique (find_vars_expr a)
    (CL.Util.list_join_unique (find_vars_expr b) (find_vars_sigma rest))
  | Slseg (a,b,_,_)::rest ->
    CL.Util.list_join_unique (find_vars_expr a)
    (CL.Util.list_join_unique (find_vars_expr b) (find_vars_sigma rest))
  | Dlseg (a,b,c,d,_,_)::rest ->
    CL.Util.list_join_unique (find_vars_expr a)
    (CL.Util.list_join_unique (find_vars_expr b) 
    (CL.Util.list_join_unique (find_vars_expr c)
    (CL.Util.list_join_unique (find_vars_expr d)
    (find_vars_sigma rest))))

(* This function provides a list of all variables used in the formula form *)
let find_vars form =
  CL.Util.list_join_unique (find_vars_sigma form.sigma) (find_vars_pi form.pi)

(*** FIND SUBFORMULA ***)
(* returns (all_vars,true)
   true if expr contains at least one variable from vars,
   all_vars are all variables in expr *)
let rec find_expr_contains_vars vars expr =
  match expr with
  | Exp.Var _ | CVar _ -> ([expr], List.mem expr vars)
  | UnOp (_,a) -> find_expr_contains_vars vars a
  | BinOp (_,a,b) ->
    let (a_vars,a_found) = find_expr_contains_vars vars a in
    let (b_vars,b_found) = find_expr_contains_vars vars b in
	let all_vars = List.append a_vars b_vars in
    (all_vars, a_found || b_found)
    | Const _ | Void | Undef -> ([],false)

let rec subpi vars pi =
  match pi with
  | [] -> ([],[])
  | Exp.BinOp (op,UnOp (Len,a),b)::tl ->
    let (a_vars,a_found) = find_expr_contains_vars vars a in
    let (tl_vars,subtl) = subpi vars tl in
    if (a_found) (* must be reach from Len *)
    then (
      let (b_vars,_) = find_expr_contains_vars vars b in
      let new_vars = CL.Util.list_diff (a_vars @ b_vars) vars in
      (CL.Util.list_join_unique new_vars tl_vars, Exp.BinOp (op,UnOp (Len,a),b)::subtl) )
    else
      (tl_vars,subtl)
  | BinOp (op,b,UnOp (Len,a))::tl ->
    let (a_vars,a_found) = find_expr_contains_vars vars a in
    let (tl_vars,subtl) = subpi vars tl in
    if (a_found) (* must be reach from Len *)
    then (
      let (b_vars,_) = find_expr_contains_vars vars b in
      let new_vars = CL.Util.list_diff (b_vars @ a_vars) vars in
      (CL.Util.list_join_unique new_vars tl_vars, BinOp (op,b,UnOp (Len,a))::subtl) )
    else
      (tl_vars,subtl)
  | expr::tl -> let (all_vars,found) = find_expr_contains_vars vars expr in
    let (tl_vars, subtl) = subpi vars tl in
    if (found) then (
      let new_vars = CL.Util.list_diff all_vars vars in
      (* print_string ("PI: ");
      print_string (CL.Util.list_to_string (Exp.to_string) new_vars);
      print_endline (Exp.to_string expr); *)
      (CL.Util.list_join_unique new_vars tl_vars, expr::subtl) )
    else
      (tl_vars, subtl)

let rec subsigma vars sigma =
  match sigma with
  | [] -> ([],[])
  | Hpointsto (a,size,b)::tl ->
    let (a_vars,a_found) = find_expr_contains_vars vars a in
    let (tl_vars,subtl) = subsigma vars tl in
    if (a_found) (* must be reach from source pointer *)
    then
      let (size_vars,_) = find_expr_contains_vars vars size in
      let (b_vars,_) = find_expr_contains_vars vars b in
      let new_vars = CL.Util.list_diff (a_vars @ size_vars @ b_vars) vars in
      (CL.Util.list_join_unique new_vars tl_vars, Hpointsto (a,size,b)::subtl)
    else
      (tl_vars,subtl)
  | Slseg (a,b,l,shared)::tl ->
    let (a_vars,a_found) = find_expr_contains_vars vars a in
    let (tl_vars,subtl) = subsigma vars tl in
    if (a_found) (* must be reach from source pointer *)
    then
      let (b_vars,_) = find_expr_contains_vars vars b in
      let new_vars = CL.Util.list_diff (a_vars @ b_vars) vars in
      (CL.Util.list_join_unique new_vars tl_vars, Slseg (a,b,l,shared)::subtl)
    else
      (tl_vars,subtl)
  | Dlseg (a,b,c,d,l,shared)::tl ->
    let (a_vars,a_found) = find_expr_contains_vars vars a in
    let (c_vars,c_found) = find_expr_contains_vars vars c in
    let (tl_vars,subtl) = subsigma vars tl in
    if (a_found)||(c_found) (* must be reach from source pointer *)
    then
      let (b_vars,_) = find_expr_contains_vars vars b in
      let (d_vars,_) = find_expr_contains_vars vars d in
      let new_vars = CL.Util.list_diff (a_vars @ b_vars @ c_vars @ d_vars) vars in
      (CL.Util.list_join_unique new_vars tl_vars, Dlseg (a,b,c,d,l,shared)::subtl)
    else
      (tl_vars,subtl)

(* returns list of all variables in subformula including vars and a subformula
   that contains only clauses with variables from vars *)
let subformula_only vars ff =
  let (pi_vars,pi_f) = subpi vars ff.pi in
  let (sigma_vars,sigma_f) = subsigma vars ff.sigma in
  ((CL.Util.list_join_unique pi_vars sigma_vars),{pi = pi_f; sigma = sigma_f})

(*  [subformula solver vars form] returns
    list of all variables that may be in subformula
    a subformula that contains clauses with variables from [vars] and related
    variables to them
    [form] - expect satisfiable formula only
    [vars] - list of FExp, but expect CVar and Var only *)
let rec subformula vars f =
  match vars with
  | [] ->
    (* print_string ("END_SUBFORMULA: "); print_endline (to_string f); *)
    (vars,empty)
  | _ ->
    let (new_vars,new_f) = subformula_only vars f in
    let (tl_vars,tl_f) = subformula new_vars (diff f new_f) in
    let all_vars = (vars @ tl_vars) in
    (* print_string ("subformula:"^CL.Util.list_to_string (Exp.to_string) vars ^ "\n");
    print_string (CL.Util.list_to_string (Exp.to_string) all_vars ^ "ALL\n"); *)
    (all_vars, disjoint_union new_f tl_f)

let var_is_reachable f uid depend_uids =
  let (subvars,_(* subf *)) = subformula [(Var uid)] f in
  let depend_vars = Exp.get_list_vars depend_uids in
  (* Config.debug4 ("subformula: "^(to_string subf));
  Config.debug4 ("sub: "^ (CL.Util.list_to_string Exp.to_string subvars)^" depends: "^ (CL.Util.list_to_string Exp.variable_to_string depend_uids)); *)
  if (CL.Util.list_inter subvars depend_vars) = [] then false else true

(**** FORMULA SIMPLIFICATION ****)
(* Function to simplify formula by removing equivalent existential variables *)

(* get a list of pair of equal variables from Pure part *)
let rec get_varmap pi =
  match pi with
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
    add_2 @ add_1 @ (get_eq_vars_ll vlist rest)

(* get all variables equivalent with a from pure part by computing a transitive
   closure *)
let get_equiv_vars a pi =
  let equalities = get_varmap pi in
  let rec get_eq_vars vlist =
    let eq = get_eq_vars_ll vlist equalities in
    match eq with
    | [] -> []
    | _ -> CL.Util.list_join_unique eq (get_eq_vars (CL.Util.list_join_unique eq vlist))
  in
  get_eq_vars a

let rec substitute_expr var1 var2 expr =
  match expr with
  | Exp.Var _ when expr=var2 -> var1
  | Var a -> Exp.Var a
  | CVar _ when expr=var2 -> var1
  | CVar a -> CVar a
  | Const a -> Const a
  | UnOp (op,a) -> UnOp (op, substitute_expr var1 var2 a)
  | BinOp (op,a,b) -> BinOp (op, substitute_expr var1 var2 a, substitute_expr var1 var2 b)
  | Void -> Void
  | Undef -> Undef

let rec substitute_sigma var1 var2 sigma =
  match sigma with
    | [] -> []
    | Hpointsto (a,l,b) ::rest ->
      let a_new = substitute_expr var1 var2 a in
      let b_new = substitute_expr var1 var2 b in
      let l_new = substitute_expr var1 var2 l in
      Hpointsto (a_new,l_new,b_new):: substitute_sigma var1 var2 rest
    | Slseg (a,b,l,shared) ::rest ->
      let a_new = substitute_expr var1 var2 a in
      let b_new = substitute_expr var1 var2 b in
      Slseg (a_new,b_new,l,shared) :: substitute_sigma var1 var2 rest
    | Dlseg (a,b,c,d,l,shared) ::rest ->
      let a_new = substitute_expr var1 var2 a in
      let b_new = substitute_expr var1 var2 b in
      let c_new = substitute_expr var1 var2 c in
      let d_new = substitute_expr var1 var2 d in
      Dlseg (a_new,b_new,c_new,d_new,l,shared) :: substitute_sigma var1 var2 rest


let rec substitute_pi var1 var2 pi =
  match pi with
  | expr::rest -> (substitute_expr var1 var2 expr) :: (substitute_pi var1 var2 rest)
  |  [] -> []


let substitute_vars_cvars var1 var2 form =
  let pi_out = substitute_pi var1 var2 form.pi in
  let sigma_out = substitute_sigma var1 var2 form.sigma in
  {sigma = sigma_out; pi = pi_out}


let rec substitute_expr_all new_vars old_vars form = 
  match new_vars, old_vars with
  | [],[] -> form
  | new_var :: new_vars_rest, old_var :: old_vars_rest -> 
    substitute_expr_all new_vars_rest old_vars_rest (substitute_vars_cvars new_var old_var form)
  | _,_ -> raise_notrace (ErrorInFormula ("Unequal length of vars during substitution",__POS__))


let substitute_vars var1 var2 form =
  substitute_vars_cvars (Var var1) (Var var2) form

let rec substitute var1 eqvarlist form =
  match eqvarlist with
  | [] -> form
  | first::rest ->
    let form1=substitute_vars var1 first form in
      substitute var1 rest form1

let list_add_unique a pi =
  let mem x =
    let eq y =
      match x, y with
      | _,_ when x=y -> true
      (* | Exp.BinOp (Peq,a,b),_ when a=b -> true *)
      | Exp.BinOp (Peq,a,b),Exp.BinOp (Peq,c,d) when a=d && b=c -> true
      | Exp.BinOp (Pneq,a,b),Exp.BinOp (Pneq,c,d) when a=d && b=c -> true
      | _ -> false
    in
    List.exists eq pi
  in
  if mem a then pi else a::pi

(* remove redundant equalities from pure part formula *)
let rec remove_redundant_eq pi =
  match pi with
  | [] -> []
  | first::rest ->
    match first with
    | Exp.BinOp (Peq,a,b) when a=b ->
      remove_redundant_eq rest
    | _ -> list_add_unique first (remove_redundant_eq rest)

(* simplify the formula, that rename equivalent variables as one and
   remove redundant equalities from pure part
   gvars - global variables, evars - existential variables *)
let remove_equiv_vars gvars evars f =
  let rec rename_eqviv_vars gvars form =
    match gvars with
    | [] -> form
    | a :: rest ->
      let eq_vars=(get_equiv_vars [a] form.pi) in
      let mem x =
        let eq y= (x=y) in
        List.exists eq evars
      in
      let eq_vars_ex = List.filter mem eq_vars in
      let form1= substitute a eq_vars_ex form in
        rename_eqviv_vars rest form1
  in
  let f_rename = rename_eqviv_vars gvars f in
  {pi = remove_redundant_eq f_rename.pi; sigma = f_rename.sigma}

(* remove usless conjuncts from pure part
   - a conjunct is useless iff
   1) contains evars only
   2) there is no transitive reference from spatial part or program variables *)

let rec get_referenced_conjuncts_ll pi ref_vars =
  let mem x =
    let eq y= (x=y) in
    List.exists eq ref_vars
  in
  let nomem x = not (mem x) in
  match pi with
  | [] -> [],[]
  | first::rest ->
      let vars_in_first=find_vars_expr first in
      let referenced=List.filter mem vars_in_first in
      let non_referenced = List.filter nomem vars_in_first in
      match referenced,non_referenced with
      | [],_ -> get_referenced_conjuncts_ll rest ref_vars
      | _,nrefs ->
        let ref_conjuncts,transitive_refs= get_referenced_conjuncts_ll rest ref_vars in
          first::ref_conjuncts, (CL.Util.list_join_unique transitive_refs nrefs)

let get_referenced_conjuncts pi referenced_vars =
  let rec get_referenced_conjuncts_rec ref_vars =
    let res,new_refs=get_referenced_conjuncts_ll pi ref_vars in
    match new_refs with
    | [] -> res
    | _ -> get_referenced_conjuncts_rec (ref_vars @ new_refs)
  in
  get_referenced_conjuncts_rec referenced_vars

(* expect satisfiable formula only *)
let remove_useless_conjuncts form evars exclude_from_refs=
  let mem to_filter x =
      let eq y= (x=y) in
      not (List.exists eq to_filter )
  in
  let vars=find_vars form in
  let gvars=List.filter (mem evars) vars in
  let ref_vars=CL.Util.list_join_unique (find_vars_sigma form.sigma)  gvars in
  let ref_vars_filtered=List.filter (mem exclude_from_refs) ref_vars in
  let new_pi=get_referenced_conjuncts form.pi ref_vars_filtered in
  {sigma=form.sigma; pi=new_pi}

(* remove empty slsegments *)
let rec remove_empty_slseg_ll sigma =
	match sigma with
	| [] -> []
	| Slseg(a,b,l,shared)::rest -> if (a=b) 
			then (remove_empty_slseg_ll rest)
			else Slseg(a,b,l,shared) :: (remove_empty_slseg_ll rest)
	| Dlseg(a,b,c,d,l,shared)::rest -> if (a=d)&&(b=c)
			then  (remove_empty_slseg_ll rest)
			else Dlseg(a,b,c,d,l,shared):: (remove_empty_slseg_ll rest)
	| first:: rest -> first::(remove_empty_slseg_ll rest)

let remove_empty_slseg form =
	let sigma_new=remove_empty_slseg_ll form.sigma in
	{sigma=sigma_new; pi=form.pi}

(* now we have everything for global simplify function,
   evars is a list of Ex. q. variables, which can be renamed/removed/etc...
   form - expect satisfiable formula only *)
let simplify form evars=
  let mem x =
    let eq y= (x=y) in
    not (List.exists eq evars )
  in
  let vars = find_vars form in
  let gvars = List.filter mem vars in
  let form1 = remove_equiv_vars gvars evars form in
  let form2 = remove_useless_conjuncts form1 evars [] in
  remove_empty_slseg form2

(* this is used in the lambda creation. 
   --- Everything related only to the referenced variables (lambda_refs) is removed from pi. 
   --- they can not be removed from sigma 
   ---> they are treated as gvars in remove_equiv_vars and 
        as nonreferenced_vars in remove_useless conjuncts *)
let simplify_lambda form evars lambda_refs=
  let mem x =
    let eq y= (x=y) in
    not (List.exists eq evars )
  in
  let vars = find_vars form in
  let gvars = List.filter mem vars in
  let form1 = remove_equiv_vars gvars evars form in
  remove_useless_conjuncts form1 evars lambda_refs

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
        let new_form = substitute_vars new_var first form in
        rename_ex_variables_ll new_form all_vars rest conflicts (new_var+1) (new_var :: new_evars)
      else rename_ex_variables_ll form all_vars rest conflicts seed (first :: new_evars)


(* create fresh names for evars with conflicts *)
let rename_ex_variables form evars conflicts =
  let all_vars = find_vars form in
  rename_ex_variables_ll form all_vars evars conflicts 1 []

(***** Unfold predicate *******)
(* for the Slseg(x,_,_) predicate given by the index pnum
   and for each Hpointsto(y,_,_) create base(x) != base(y) 
   skip if we use closed lambdas
   *)

(*
let rec diffbase_ll sigma x =
  match sigma with
  | [] -> []
  | first::rest ->
    match first with
    | Hpointsto (a,_,_) ->
      let base_x=Exp.UnOp (Base, x) in
      let base_a=Exp.UnOp (Base, a) in
      Exp.BinOp (Pneq,base_a,base_x) :: diffbase_ll rest x
    | Slseg _ | Dlseg _ -> diffbase_ll rest x

let diffbase form pnum dir =
  if Config.close_lambda () then [] 
  else
  match (List.nth form.sigma pnum),dir with
  | Slseg (x,_,_),1 | Dlseg(x,_,_,_,_),1 | Dlseg (_,_,x,_,_),2 ->
    let nequiv a b = not (a=b) in
    let remove k lst = List.filter (nequiv (List.nth lst k)) lst in
    let sigma= remove pnum form.sigma in
    diffbase_ll sigma x
  | _ -> []
*)

let diffbase _ _ _ = []

(* The predicate pnum is removed from form.sigma, unfolded once and all the new stuff is added to the end of the list form.sigma,
   !!! The function Abstraction.try_add_slseg_to_pointsto relies on the fact, that the unfolded stuff is added to the end 

  dir (in case of Dlseg): 1 - from begining, 2 - from end. *)
  (* pnum = pointer number in form.sigma*)
  (* the unfolding introduces a fresh variable for an evar in the lambda iff that evar is not 
  in 'conflicts' and does not occur in 'form' *)
let unfold_predicate form pnum conflicts dir =
  let confl=CL.Util.list_join_unique conflicts (find_vars form) in
  let nequiv a b = not (a=b) in
  let remove k lst = List.filter (nequiv (List.nth lst k)) lst in
  let rec get_fresh_var s confl=
    if (List.mem s confl)
    then get_fresh_var (s+1) confl
    else s
  in
  let nomem lst x = not (List.mem x lst) in
  match (List.nth form.sigma pnum) with
  | Slseg (a,b,lambda,shared) -> 
    let confl1=confl @ (find_vars lambda.form) in
    let l_evars=List.filter (nomem lambda.param) (find_vars lambda.form) in
    let (l_form1,added_vars) = rename_ex_variables lambda.form l_evars confl in
    let new_a = (get_fresh_var (List.nth lambda.param 0) (confl1 @ added_vars) ) in
    let new_b = (get_fresh_var (new_a + 1) (new_a::(confl1 @ added_vars))) in
    (* instantiate all params adequately *)
    let l_form2 = substitute_expr_all ([(Exp.Var new_a); (Exp.Var new_b)] @ shared) 
      (List.map (fun x -> Exp.Var x) lambda.param) l_form1 in
    let res_form=simplify
      {sigma = (remove pnum form.sigma)@ l_form2.sigma @ [Slseg (Var new_b,b,lambda,shared)];
       pi=form.pi @ l_form2.pi @ [Exp.BinOp (Peq,a,Var new_a)] @ (diffbase form pnum 1) }
      ([new_a;new_b]@added_vars) in
    (* find the newly added logical variables as (find_vars res_form) \setminus (find_vars form) *)
    let new_lvars=List.filter  (nomem (find_vars form)) (find_vars res_form) in
    res_form, new_lvars
  | Dlseg (a,b,c,d,lambda,shared) ->
    let confl1=confl @ (find_vars lambda.form) in
    let l_evars=List.filter (nomem lambda.param) (find_vars lambda.form) in
    let (l_form1,added_vars) = rename_ex_variables lambda.form l_evars confl in
    let new_a = (get_fresh_var (List.nth lambda.param 0) (confl1 @ added_vars) ) in
    let new_b = (get_fresh_var (new_a + 1) (new_a::(confl1 @ added_vars))) in
    let new_c = (get_fresh_var (new_b + 1) ([new_a;new_b] @ confl1 @ added_vars)) in
    let l_form2= substitute new_a [(List.nth lambda.param 0)] l_form1 in
    let l_form3 = substitute new_b [(List.nth lambda.param 1)] l_form2 in
    let l_form4 = substitute new_c [(List.nth lambda.param 2)] l_form3 in
    let res_form=
    	if dir=1 
	then simplify
      		{sigma = (remove pnum form.sigma)@ l_form4.sigma @ [Dlseg (Var new_b,Var new_a,c,d,lambda,shared)];
       		pi=form.pi @ l_form4.pi @ [Exp.BinOp (Peq,a,Var new_a);Exp.BinOp (Peq,b,Var new_c)] @ (diffbase form pnum 1) }
      		([new_a;new_b;new_c]@added_vars) 
	else simplify
      		{sigma = (remove pnum form.sigma)@ l_form4.sigma @ [Dlseg (a,b,Var new_c,Var new_a,lambda,shared)];
       		pi=form.pi @ l_form4.pi @ [Exp.BinOp (Peq,c,Var new_a);Exp.BinOp (Peq,d,Var new_b)] @ (diffbase form pnum 2) }
      		([new_a;new_b;new_c]@added_vars)
		
	in
    (* find the newly added logical variables as (find_vars res_form) \setminus (find_vars form) *)
    let new_lvars=List.filter  (nomem (find_vars form)) (find_vars res_form) in
    res_form, new_lvars
  | _ -> form,[] (* wrong parameters => no unfolding *)

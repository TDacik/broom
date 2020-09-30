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
      | Freed    (** for heap allocation *)
      | Invalid  (** for stack allocation *)
      | BVnot    (** bitwise, in C: ~ *)
      | Pnot     (** logical, in C: ! *)
      | Puminus  (** in C: - *)

    (* aritmetic operation *)
    and binop =
        Stack    (** stack allocation Stack(ptr,obj): ptr-(_)->obj *)
      | Static   (** static storage Static(ptr,obj): ptr-(_)->obj *)
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
  | _ -> assert false

let rec to_string ?lvars:(lvars=[]) e =
  match e with
  | Var a -> variable_to_string ~lvars:lvars a
  | CVar a -> cvariable_to_string a
  | Const a -> const_to_string a
  | UnOp (op,a) -> unop_to_string op ^ "(" ^ to_string ~lvars:lvars a ^ ")"
  | BinOp (op,a,b) -> (
    match op with
    | Stack ->
      "stack(" ^ to_string ~lvars:lvars a ^", "^ to_string ~lvars:lvars b ^ ")"
    | Static ->
      "static(" ^ to_string ~lvars:lvars a ^", "^ to_string ~lvars:lvars b ^ ")"
    | _ -> "(" ^ to_string ~lvars:lvars a ^ binop_to_string op ^
    to_string ~lvars:lvars b ^ ")" )
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
  | Slseg of Exp.t * Exp.t * lambda    (* source, destination, lambda *)
  (* todo *)

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
    | Hpointsto (a,l,b) -> (
      Exp.to_string ~lvars:lvars a ^" -("^
      (Exp.to_string ~lvars:lvars l) ^")->"^
      Exp.to_string ~lvars:lvars b), ""
    | Slseg (a,b,lambda) ->
      let lambda_id= "lambda-"^(string_of_int lambda_level)^":"^(string_of_int num) in
      ("Slseg(" ^ Exp.to_string ~lvars:lvars a ^", "^
        Exp.to_string ~lvars:lvars b ^", "^
        lambda_id^") "),
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

(*** FIND ALL VARIABLES IN FORMULA ***)

(* returns: ptr new_sigma new_cvars *)
let rec find_and_remove_var_pointsto obj sigma cvars =
  match sigma with
  | [] -> let cvar_last = cvars + 1 in
    (Exp.CVar cvar_last), [], cvar_last
  | Hpointsto (ptr,size,obj)::rest -> (
    match ptr with
    | Var _ | CVar _ -> (ptr, rest, cvars)
    | _ ->
      let (ptr0,sig0,cvars0) = find_and_remove_var_pointsto obj rest cvars in
      ptr0, Hpointsto (ptr,size,obj)::sig0, cvars0 )
  | exp::rest ->
    let (ptr0,sig0,cvars0) = find_and_remove_var_pointsto obj rest cvars in
    ptr0, exp::sig0, cvars0

(* exexcept contract variables *)
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
  | Slseg (a,b,_)::rest ->
    CL.Util.list_join_unique (find_vars_expr a)
    (CL.Util.list_join_unique (find_vars_expr b) (find_vars_sigma rest))

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
  | expr::tl -> let (all_vars,found) = find_expr_contains_vars vars expr in
    let (tl_vars, subtl) = subpi vars tl in
    if (found) then
      let new_vars = CL.Util.list_diff all_vars vars in
      (CL.Util.list_join_unique new_vars tl_vars, expr::subtl)
    else
      (tl_vars, subtl)

let rec subsigma vars sigma =
  match sigma with
  | [] -> ([],[])
  | Hpointsto (a,size,b)::tl ->
    let (a_vars,a_found) = find_expr_contains_vars vars a in
    let (size_vars,_) = find_expr_contains_vars vars size in
    let (b_vars,_) = find_expr_contains_vars vars b in
    let (tl_vars,subtl) = subsigma vars tl in
    if (a_found) (* must be reach from source pointer *)
    then
      let new_vars = CL.Util.list_diff (a_vars @ size_vars @ b_vars) vars in
      (CL.Util.list_join_unique new_vars tl_vars, Hpointsto (a,size,b)::subtl)
    else
      (tl_vars,subtl)
  | Slseg (a,b,l)::tl ->
    let (a_vars,a_found) = find_expr_contains_vars vars a in
    let (b_vars,_) = find_expr_contains_vars vars b in
    let (tl_vars,subtl) = subsigma vars tl in
    if (a_found) (* must be reach from source pointer *)
    then
      let new_vars = CL.Util.list_diff (a_vars @ b_vars) vars in
      (CL.Util.list_join_unique new_vars tl_vars, Slseg (a,b,l)::subtl)
    else
      (tl_vars,subtl)

(* returns a subformula that contains clauses with variables from vars and
   related variables to them and list of all variables that may be in
   subformula and flag if something was removed from spatial part
   form - expect satisfiable formula only
   vars - list of Exp, but expect CVar and Var only *)
let rec subformula vars f =
  (* returns a subformula that contains only clauses with variables from vars
     and list of all variables in subformula expect vars *)
  let subformula_only only_vars ff =
    let (pi_vars,pi_f) = subpi only_vars ff.pi in
    let (sigma_vars,sigma_f) = subsigma only_vars ff.sigma in
    ((CL.Util.list_join_unique pi_vars sigma_vars),{pi = pi_f; sigma = sigma_f})
  in

  match vars with
  | [] ->
	  (* print_string ("END\n"); *)
    let removed_sigma = if (f.sigma = []) then false else true in
    (removed_sigma,vars,empty)
  | _ ->
    let (new_vars,new_f) = subformula_only vars f in
    let (flag,tl_vars,tl_f) = subformula new_vars (diff f new_f) in
    let all_vars = (vars @ tl_vars) in
	  (* print_string ("subformula:"^CL.Util.list_to_string (Exp.to_string) vars ^ "\n");
	  print_string (CL.Util.list_to_string (Exp.to_string) all_vars ^ "ALL\n"); *)
    (flag,all_vars, disjoint_union new_f tl_f)

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
  | _ -> CL.Util.list_join_unique eq (get_eq_vars (CL.Util.list_join_unique eq vlist) equalities)


let rec substitute_expr var1 var2 expr =
  match expr with
  | Exp.Var a ->
    ( match var2 with
      | Exp.Var v2 -> if (a=v2) then var1 else Exp.Var a
      | _ -> Exp.Var a )
  | CVar a ->
    ( match var2 with
      | Exp.CVar v2 -> if (a=v2) then var1 else Exp.CVar a
      | _ -> Exp.CVar a )
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
      Hpointsto (a_new,l_new,b_new) :: substitute_sigma var1 var2 rest
    | Slseg (a,b,l) ::rest ->
      let a_new = substitute_expr var1 var2 a in
      let b_new = substitute_expr var1 var2 b in
      Slseg (a_new,b_new,l) :: substitute_sigma var1 var2 rest


let rec substitute_pi var1 var2 pi =
  match pi with
  | expr::rest -> (substitute_expr var1 var2 expr) :: (substitute_pi var1 var2 rest)
  |  [] -> []


let substitute_vars_cvars var1 var2 form =
  let sigma_out = substitute_sigma var1 var2 form.sigma in
  let pi_out = substitute_pi var1 var2 form.pi in
  {sigma = sigma_out; pi = pi_out}


let substitute_vars var1 var2 form =
  substitute_vars_cvars (Var var1) (Var var2) form


let rec substitute var1 eqvarlist form =
  match eqvarlist with
  | [] -> form
  | first::rest ->
    let form1=substitute_vars var1 first form in
      substitute var1 rest form1

(* remove redundant equalities from pure part formula *)
let rec remove_redundant_eq pi =
  match pi with
  | [] -> []
  | first::rest ->
    match first with
    | Exp.BinOp (Peq,a,b) when a=b ->
      remove_redundant_eq rest
    | _ -> first :: (remove_redundant_eq rest)

(* simplify the formula, that rename equivalent variables as one and
   remove redundant equalities from pure part
   gvars - global variables, evars - existential variables *)
let remove_equiv_vars gvars evars f =
  let rec rename_eqviv_vars gvars form =
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
        rename_eqviv_vars rest form1
  in
  let f_rename = rename_eqviv_vars gvars f in
  {pi = remove_redundant_eq f_rename.pi; sigma = f_rename.sigma}

(* remove usless conjuncts from pure part
   - a conjunct is useless iff
   1a) contains evars only
   1b) it is of the form exp1 !=exp2 and evars  are not togather with ref_vars in exp1/2
      --- r1 != e1 (r1 referenced, e1 existential) => this conjunct is not needed
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
    match first with
    | Exp.BinOp ( Pneq, a, b) -> ( (* handle the case 1b *)
      let a_vars=find_vars_expr a in
      let b_vars=find_vars_expr b in
      let referenced_a=List.filter mem a_vars in
      let referenced_b=List.filter mem b_vars in
      let non_referenced_a = List.filter nomem a_vars in
      let non_referenced_b = List.filter nomem b_vars in
      match referenced_a,referenced_b,non_referenced_a,non_referenced_b with
      | [],[],_,_ -> get_referenced_conjuncts_ll rest ref_vars
      | _,[],[],_ -> get_referenced_conjuncts_ll rest ref_vars
      | [],_,_,[] -> get_referenced_conjuncts_ll rest ref_vars
      | _,_,nrefs_a,nrefs_b ->
        let ref_conjuncts,transitive_refs= get_referenced_conjuncts_ll rest ref_vars in
          first::ref_conjuncts, (CL.Util.list_join_unique transitive_refs (CL.Util.list_join_unique nrefs_a nrefs_b))
    )
    | _ ->
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
let remove_useless_conjuncts form evars =
  let mem x =
      let eq y= (x=y) in
      not (List.exists eq evars )
  in
  let vars=find_vars form in
  let gvars=List.filter mem vars in
  let ref_vars=CL.Util.list_join_unique (find_vars_sigma form.sigma)  gvars in
  let new_pi=get_referenced_conjuncts form.pi ref_vars in
  {sigma=form.sigma; pi=new_pi}

(* fixed_vars - variables can't be removed
   form - expect satisfiable formula only *)
let simplify2 fixed_vars form =
  let fixed_vars_exp = Exp.get_list_vars fixed_vars in
  let (removed_sigma,all_vars,subf) = subformula fixed_vars_exp form in
  let evars = CL.Util.list_diff (Exp.get_list_uids all_vars) fixed_vars in
  (removed_sigma,remove_equiv_vars fixed_vars evars subf)

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
  remove_useless_conjuncts form1 evars


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

let rec diffbase_ll sigma x =
  match sigma with
  | [] -> []
  | first::rest ->
    match first with
    | Hpointsto (a,_,_) ->
      let base_x=Exp.UnOp (Base, x) in
      let base_a=Exp.UnOp (Base, a) in
      Exp.BinOp (Pneq,base_a,base_x) :: diffbase_ll rest x
    | Slseg _ -> diffbase_ll rest x

(* for the Slseg(x,_,_) predicate given by the index pnum
   and for each Hpointsto(y,_,_) create base(x) != base(y) *)
let diffbase form pnum =
  match (List.nth form.sigma pnum) with
  | Hpointsto _ -> []
  | Slseg (x,_,_) ->
    let nequiv a b = not (a=b) in
    let remove k lst = List.filter (nequiv (List.nth lst k)) lst in
    let sigma= remove pnum form.sigma in
    diffbase_ll sigma x

(* The predicate pnum is removed from form.sigma, unfolded once and all the new stuff is added to the end of the list form.sigma,
   !!! The function Abstraction.try_add_slseg_to_pointsto relies on the fact, that the unfolded stuff is added to the end *)
let unfold_predicate form pnum conflicts =
  let confl=CL.Util.list_join_unique conflicts (find_vars form) in
  let nequiv a b = not (a=b) in
  let remove k lst = List.filter (nequiv (List.nth lst k)) lst in
  let mem lst x =
    let eq y= (x=y) in
    List.exists eq lst
  in
  let rec get_fresh_var s confl=
    if (mem confl s)
    then get_fresh_var (s+1) confl
    else s
  in
  let nomem lst x = not (mem lst x) in
  match (List.nth form.sigma pnum) with
  | Hpointsto _ -> form,[]
  | Slseg (a,b,lambda) ->
    let confl1=confl @ (find_vars lambda.form) in
    let l_evars=List.filter (nomem lambda.param) (find_vars lambda.form) in
    let (l_form1,added_vars) = rename_ex_variables lambda.form l_evars confl in
    let new_a = (get_fresh_var (List.nth lambda.param 0) (confl1 @ added_vars) ) in
    let new_b = (get_fresh_var (new_a + 1) (new_a::(confl1 @ added_vars))) in
    let l_form2= substitute new_a [(List.nth lambda.param 0)] l_form1 in
    let l_form3 = substitute new_b [(List.nth lambda.param 1)] l_form2 in
    let res_form=simplify
      {sigma = (remove pnum form.sigma)@ l_form3.sigma @ [Slseg (Var new_b,b,lambda)];
       pi=form.pi @ l_form3.pi @ [Exp.BinOp (Peq,a,Var new_a)] @ (diffbase form pnum) }
      ([new_a;new_b]@added_vars) in
    (* find the newly added logical variables as (find_vars res_form) \setminus (find_vars form) *)
    let new_lvars=List.filter  (nomem (find_vars form)) (find_vars res_form) in
    res_form, new_lvars

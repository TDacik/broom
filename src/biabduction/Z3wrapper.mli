exception NoZ3Translation of string

(* width of the bitvector TODO: as a config parameter *)
val bw_width : int

(** The functions base, len, size, onstack, etc in separation logic are used as
    uninterpreted functions in Z3 *)
type sl_function_names_z3 = {
  base : Z3.FuncDecl.func_decl;
  len : Z3.FuncDecl.func_decl;
  alloc : Z3.FuncDecl.func_decl;
  onstack : Z3.FuncDecl.func_decl;
  static : Z3.FuncDecl.func_decl;
}

type solver = {
  ctx : Z3.context;
  solv : Z3.Solver.solver;
  z3_names : sl_function_names_z3;
}

val config_solver : unit -> solver

(** [create_ex_quantifier ctx evars form] creates existential quantifier
    ctx - Z3context, evars - a list of variables for quantification, form - Z3
    expressions *)
val create_ex_quantifier : Z3.context -> Z3.Expr.expr list ->
                           Z3.Expr.expr -> Z3.Expr.expr

(** [expr_to_solver_only_exp ctx func expr] translates [expr] of separation
    logic into an expression in Z3 *)
val expr_to_solver_only_exp : Z3.context -> sl_function_names_z3 ->
                              Formula.Exp.t -> Z3.Expr.expr

(** [formula_to_solver ctx form] translates separation logic formula into Z3
    solver internal representation *)
val formula_to_solver : Z3.context -> Formula.t -> Z3.Expr.expr list

(** [formula_to_solver_with_quantified_undefs ctx form] translates formula into
    Z3 solver internal representation, but for each UNDEF in the formula form,
    an fresh Z3 variable is created. 
    This function add an existential quantifier for each such a variable. 
    It is needed, when the formula is being placed on the RHS of an
    implication. When you call only formula_to_solver, a valid implication with
    UNDEFs can be evaluated as invalid. *)
val formula_to_solver_with_quantified_undefs : Z3.context -> Formula.t ->
                                               Z3.Expr.expr list

(** [query_to_string exprs] gets Z3 formula as a string *)
val query_to_string : Z3.Expr.expr list -> string

(** [check_all_lambdas ctx solv sigma] checks all lambda within the Slseg
    predicates,
    returns **true** iff the lambdas satisfy the basic properties *)
val check_all_lambdas : Z3.context -> Z3.Solver.solver -> Formula.sigma -> bool

(** [check_eq_base solver form_z3 a base_ptr] checks, if
    form_z3 & not(base(a) = base(base_ptr)) is unsatisfiable *)
val check_eq_base : solver -> Z3.Expr.expr list -> Formula.Exp.t ->
                    Formula.Exp.t -> bool

(* UNUSED *)
val mk_bv2bool : Z3.context -> Z3.Expr.expr -> Z3.Expr.expr

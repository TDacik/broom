#require "z3";;
open Z3;;
open Z3.Symbol;;
open Z3.Sort;;
open Z3.Arithmetic;;

let cfg = [("model", "true"); ("proof", "false")];;
let ctx = (mk_context cfg);;

utop # let solver2
 = (mk_solver ctx None);;
val solver2 : solver = <abstr>
─( 13:24:00 )─< command 58 >───────────────────────────────────────────────────────────────────────────────────────────────────────{ counter: 0 }─
utop # let trivial_eq = (mk_eq ctx fapp fapp) in 
Solver.add solver2 [ trivial_eq ];;
- : unit = ()
─( 13:29:37 )─< command 59 >───────────────────────────────────────────────────────────────────────────────────────────────────────{ counter: 0 }─
utop # check solver2 [];;
- : status = SATISFIABLE
─( 13:31:06 )─< command 60 >───────────────────────────────────────────────────────────────────────────────────────────────────────{ counter: 0 }─
utop # let trivial_eq = (mk_eq ctx fapp fapp);;
val trivial_eq : expr = <abstr>
─( 13:50:43 )─< command 62 >───────────────────────────────────────────────────────────────────────────────────────────────────────{ counter: 0 }─
utop # Expr.to_string;;
- : expr -> string = <fun>
─( 13:50:57 )─< command 63 >───────────────────────────────────────────────────────────────────────────────────────────────────────{ counter: 0 }─
utop # Expr.to_string trivial_eq;;
- : string = "(= (f x y) (f x y))"
─( 13:51:19 )─< command 64 >───────────────────────────────────────────────────────────────────────────────────────────────────────{ counter: 0 }─
utop # let nontrivial_eq = (mk_eq ctx fapp fapp2);;
val nontrivial_eq : expr = <abstr>
─( 13:51:28 )─< command 65 >───────────────────────────────────────────────────────────────────────────────────────────────────────{ counter: 0 }─
utop # Expr.to_string nontrivial_eq;;
- : string = "(= (f x y) (fp!1 cp!0))"
─( 13:51:57 )─< command 66 >───────────────────────────────────────────────────────────────────────────────────────────────────────{ counter: 0 }─
utop # fargs2;;
- : expr list = [<abstr>]
─( 13:52:13 )─< command 67 >───────────────────────────────────────────────────────────────────────────────────────────────────────{ counter: 0 }─
utop # Expr.to_string fargs2;;
Error: This expression has type expr list
       but an expression was expected of type expr
─( 13:54:39 )─< command 69 >───────────────────────────────────────────────────────────────────────────────────────────────────────{ counter: 0 }─
utop # List.map (fun a -> Expr.to_string a) fargs2;;
- : string list = ["cp!0"]

!!! Poznanka: promenna cp!0 byla vytvorena volanim mk_fresh_const ---> to pridalo unikatni koncovku "!0" Stejne tak fp!1 vniklo volanim
!!! mk_fresh_fun.

--------------------------
let a = mk_func_decl ctx (Symbol.mk_string ctx "a") [] (Integer.mk_sort ctx);;
let b = mk_func_decl ctx (Symbol.mk_string ctx "b") [] (Integer.mk_sort ctx);;
let aa=mk_app ctx a [];;
let bb=mk_app ctx b [];;
let eq=Boolean.mk_eq ctx aa bb;;
let solver = (mk_solver ctx None);;
check solver [eq];;
Solver.add solver [eq];;
check solver [];;
check solver [Boolean.mk_not ctx eq];;

--------------------------------
let a = (Expr.mk_const ctx (Symbol.mk_string ctx "a") (Integer.mk_sort ctx));;
let b = (Expr.mk_const ctx (Symbol.mk_string ctx "b") (Integer.mk_sort ctx));;
let eq=Boolean.mk_eq ctx a b;;
let neq=Boolean.mk_not ctx eq
let j=Integer.mk_numeral_i ctx 1
let plus=Arithmetic.mk_add ctx [a; j];;
let eq=Boolean.mk_eq ctx a plus;;
check solver [mk_not ctx eq];;

---------------------------------

let a=Quantifier.mk_bound ctx 0 (Integer.mk_sort ctx);;
let b=Quantifier.mk_bound ctx 1 (Integer.mk_sort ctx);;
let x=Boolean.mk_eq ctx a b;;
let q=Quantifier.mk_forall ctx [(Integer.mk_sort ctx); (Integer.mk_sort ctx)] [ (Symbol.mk_string ctx "x_0");(Symbol.mk_string ctx "x_1")] x (Some 1) [] [] (Some (Symbol.mk_string ctx "Q1")) (Some (Symbol.mk_string ctx "skid1"));;
Quantifier.to_string q;;
Quantifier.expr_of_quantifier q;;

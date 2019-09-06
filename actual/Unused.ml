
let create_global_restrictions ctx names_z3 =
       (* forall x: (x - base(x)) + len(x) = len( base(x)) *)
       let x=Quantifier.mk_bound ctx 0 (Integer.mk_sort ctx) in
       let l=Arithmetic.mk_add ctx [ (Arithmetic.mk_sub ctx [x;(Expr.mk_app ctx names_z3.base [x] )]); (Expr.mk_app ctx names_z3.len [x]) ] in
       let r=Expr.mk_app ctx names_z3.len [ (Expr.mk_app ctx names_z3.base [x]) ] in
       let eq = Boolean.mk_eq ctx l r in
       let q=Quantifier.mk_exists ctx [(Integer.mk_sort ctx)] [ (Symbol.mk_string ctx "x")] eq 
               (Some 1) [] [] (Some (Symbol.mk_string ctx "Q1")) (Some (Symbol.mk_string ctx "skid1")) in
       [ Quantifier.expr_of_quantifier q]


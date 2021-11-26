exception ErrorInLambdaClosing of Config.src_pos

(** [close_lambda in out] does
   - for each allocate block within lambda add pointsto(s) to fill the whole
     block (if needed) 
   - the lambda then contains whole blocks only
   - INPUT example: x -(8) -> _ * x+16 -(8)-> _ & base(x)=x
   - OUTPUT example: x -(8) -> _ * x+8 -(8)-> _ * x+16 -(8)-> _ *
                     x+24 -(len(x)-24)-> _ & base(x)=x 
*)
val close_lambda : Formula.lambda -> Formula.lambda

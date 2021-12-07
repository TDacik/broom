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

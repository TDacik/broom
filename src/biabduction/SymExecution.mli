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

(** Top level algorith of the symbolic execution. *)

(** [exec_fnc fnc_tbl f] runs the symbolic execution for function [f] and
    result summaries are store in [fnc_tbl]. If an internal error occures, all
    summaries for this function are removed and replace with one 'unfinished'
    summary. 
    @param fnc_tbl Table storing all summaries for all analysed functions 
    @param f function;  if it is 'main', global variables are initialized *)
val exec_fnc : SpecTable.t -> CL.Fnc.t -> unit

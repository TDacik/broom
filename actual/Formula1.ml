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

let equal_kind = [%compare.equal: kind]

(* all variables  *)
module Set = Caml.Set.Make (struct
  type t = name
  let compare = compare
end)

(* map from logic vars --> to program vars [registers and memory] *)
module Map = Caml.Map.Make (struct
  type t = int
  let compare = compare
end)

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

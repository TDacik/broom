open Z3

let mk_sort = Boolean.mk_sort

let mk_true = Boolean.mk_true

let mk_false = Boolean.mk_false

let mk_val = Boolean.mk_val

let mk_not = Boolean.mk_not

let mk_and = Boolean.mk_and

let mk_or = Boolean.mk_or

let mk_xor = Boolean.mk_xor

let mk_implies = Boolean.mk_implies

let mk_ite = Boolean.mk_ite

let mk_eq = Boolean.mk_eq

(*****************************************************************************)


(*
(* width of the bitvector *)
let bw_width = 64 (* 1 *)

let mk_sort ctx = BitVector.mk_sort ctx bw_width

let mk_true ctx = BitVector.mk_numeral ctx "-1" bw_width

let mk_false ctx = BitVector.mk_numeral ctx "0" bw_width

let mk_val ctx a =
	match a with
	| true -> mk_true ctx
	| false -> mk_false ctx

let mk_not ctx a = BitVector.mk_not ctx a

let rec mk_and ctx conj =
	match conj with
	| [a] -> a
	| [a;b] -> BitVector.mk_and ctx a b
	| a::tl -> BitVector.mk_and ctx a (mk_and ctx tl)
	| _ -> assert false

let rec mk_or ctx disj =
	match disj with
	| [a] -> a
	| [a;b] -> BitVector.mk_or ctx a b
	| a::tl -> BitVector.mk_or ctx a (mk_or ctx tl)
	| _ -> assert false

let mk_xor ctx a b = BitVector.mk_xor ctx a b

let mk_implies ctx a b = BitVector.mk_or ctx (mk_not ctx a) b

let mk_eq ctx a b =
	BitVector.mk_and ctx (BitVector.mk_sle ctx a b) (BitVector.mk_sge ctx a b)

*)

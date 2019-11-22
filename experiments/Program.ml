(* newer lib: Atdgen_runtime.Util *)
(*module AGU = Ag_util*)
module AGU= Atdgen_runtime.Util

(* Print function's name from association list *)
let print_name_fnc fncmap uid =
    let f = List.assoc uid fncmap in
        let op_data = f.Fnc.def.data in
          let str = ( match op_data with
              | OpCst { cst_data } -> ( match cst_data with
                  | CstFnc {uid; name; is_extern; loc} -> ( match name with
                      | Some x -> x
                      | None -> "" )
                      (* Option.is_none / Option.is_some *)
                  | _ -> raise Not_found )
              | _ -> raise Not_found ) in
          Printf.printf "%s\n" str

(* Print variable's name from association list *)
let print_name_var vmap uid = 
    let v = List.assoc uid vmap in
        ( match v.Var.name with
        | Some x -> Printf.printf "%s\n" x
        | None -> Printf.printf "\n" )


(*
ppx_fields_conv               v0.11.0  Generation of accessor and iteration functions for ocaml records
ppx_variants_conv             v0.11.0  Generation of accessor and iteration functions for ocaml variant types
    
*)

(* zistit, ci sa v module da pracovat s jeho typom (private val), bez
 pouzivania v parametroch funkcie *)
(* module Program = struct *)
    type t = Storage.t

    (* vmap = Storage.vars  ???? *)
    
    (* read program into storage from stdin - private? *)
    (*let p = AGU.Json.from_channel Storage.read_t stdin*)
    let p= AGU.Json.from_file Storage.read_t "../tests/sll1.json"

    (* Get program variable by uid *)
    let get_pvar vmap uid = List.assoc uid vmap
(* end *)

(* * * * * * * * * * * * * * * main * * * * * * * * * * * * * * *)
let () =
    Printf.printf "............Analysing function: ";
    let (fst_fnc_uid, fst_fnc) = List.hd p.fncs in
    print_name_fnc p.fncs fst_fnc_uid;
    print_newline ();

(* * * * * * * * * * * * * * * main * * * * * * * * * * * * * * *)
let () =
	let (_, fnc) = List.hd CL.Util.stor.fncs in
	Biabd.SymExecution.exec_fnc fnc


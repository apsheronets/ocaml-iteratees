(*
value dbg fmt = Printf.printf fmt
;
*)

value dbg fmt = Printf.ifprintf Pervasives.stdout fmt
;

type place = string;

(* +
   Sometimes it's more convenient to have an IO result wrapped
   in value with type [res 'a], than having to [IO.catch] errors.
   See function [mres] in functor.
*)

type res 'a = [= `Ok of 'a | `Error of (exn * place) ]
;

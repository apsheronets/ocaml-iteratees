(* +
   The [place] type represents the place where exception
   was raised.  For now, it's a name of IO function returned
   an error.
*)

type place = string;


(* +
   This is a signature for IO monad.  These functions and types are used
   by Iteratees functor.  It's possible that your implementation of IO
   have much more functions than MonadIO, so you should not restrict
   your IO implementation by this MonadIO signature.
*)

module type MonadIO
 =
  sig
    type m 'a;
    value return : 'a -> m 'a;
    value bind : ('a -> m 'b) -> m 'a -> m 'b;

    value error : (exn * place) -> m 'a;
    value catch : (unit -> m 'a) -> ((exn * place) -> m 'a) -> m 'a;

    type output_channel;
    value stdout : output_channel;
    value write : output_channel -> string -> m unit;

    type input_channel;
    value open_in : string -> m input_channel;
    value close_in : input_channel -> m unit;  (* Lwt_io.close inch *)
    value read_into : input_channel -> string -> int -> int -> m int;
       (* in lwt: read_into ic buffer offset length *)
  end
;


(* +
   Sometimes it's more convenient to have an IO result wrapped
   in value with type [res 'a], than having to [IO.catch] errors.
   See function [mres] in functor.
*)

type res 'a = [= `Ok of 'a | `Error of (exn * place) ]
;

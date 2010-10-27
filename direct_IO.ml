open Types
;

(* OCaml Pervasives IO *)

value res_of_exn ep : res 'a = `Error ep
;

module Direct_IO
 :
  sig
    type m 'a = res 'a;

    value return : 'a -> m 'a;
    value bind : ('a -> m 'b) -> m 'a -> m 'b;
    value catch : (unit -> m 'a) -> ((exn * place) -> m 'a) -> m 'a;

    value error : (exn * place) -> m 'a;

    type output_channel;
    value stdout : output_channel;
    value write : output_channel -> string -> m unit;

    type input_channel;
    value open_in : string -> m input_channel;
    value close_in : input_channel -> m unit;  (* Lwt_io.close inch *)
    value read_into : input_channel -> string -> int -> int -> m int;
       (* read_into ic buffer offset length *)

    value runIO : m 'a -> res 'a;

  end
 =
  struct
    type m 'a = res 'a;
    value return x = `Ok x;
    value bind f m =
      match m with
      [ `Ok r -> f r
      | `Error ep -> `Error ep
      ]
    ;
    value ( >>= ) m f = bind f m;

    value catch f handler =
      match f () with
      [ (`Ok _) as r -> r
      | `Error ep -> handler ep
      ]
    ;

(*
    value try_bind m f handler =
      catch (fun () -> m () >>= f) handler
    ;
*)

(*
    value read_into in_ch buf ofs len = fun () ->
      try `Ok (Pervasives.input in_ch buf ofs len)
      with [ e -> res_of_exn e ]
    ;
*)
    value wrap1 place f = fun a ->
      try `Ok (f a)
      with [ e -> res_of_exn (e, place) ]
    ;
    value wrap2 place f = fun a b ->
      try `Ok (f a b)
      with [ e -> res_of_exn (e, place) ]
    ;
    value wrap4 place f = fun a b c d ->
      try `Ok (f a b c d)
      with [ e -> res_of_exn (e, place) ]
    ;

    value read_into = wrap4 "read_into" Pervasives.input;

    value error = res_of_exn;

    type output_channel = Pervasives.out_channel;
    value stdout = Pervasives.stdout;
    value write = wrap2 "write" Pervasives.output_string;

    type input_channel = Pervasives.in_channel;
    value open_in = wrap1 "open_in" Pervasives.open_in_bin;
    value close_in = wrap1 "close_in" Pervasives.close_in;

    value runIO x = x;

  end
;

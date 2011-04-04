open Types
;

(* Lwt IO *)

module It_Lwt_IO
 :
  sig
    type m +'a = Lwt.t 'a;

    value return : 'a -> m 'a;
    value bind : ('a -> m 'b) -> m 'a -> m 'b;
    value catch : (unit -> m 'a) -> (exn -> m 'a) -> m 'a;

    value error : exn -> m 'a;

    type output_channel = Lwt_io.output_channel;
    value stdout : output_channel;
    value write : output_channel -> string -> m unit;

    type input_channel = Lwt_io.input_channel;
    value open_in : string -> m input_channel;
    value close_in : input_channel -> m unit;  (* Lwt_io.close inch *)
    value read_into : input_channel -> string -> int -> int -> m int;
       (* read_into ic buffer offset length *)

    value runIO : m 'a -> res 'a;

    value with_file_in_bin : string -> (input_channel -> m 'a) -> m 'a;
    value with_file_out_bin : string -> (output_channel -> m 'a) -> m 'a;

  end
 =
  struct
    type m +'a = Lwt.t 'a;
    value return = Lwt.return;
    value bind f m = Lwt.bind m f;
    value ( >>= ) = Lwt.bind;

    value catch = Lwt.catch;

(*
    value try_bind m f handler =
      catch (fun () -> m () >>= f) handler
    ;
*)


    value wrap_exn place = fun e ->
      Lwt.fail (EIO (e, place))
    ;


    value wrap1 place f = fun a ->
      catch (fun () -> f a)
      (wrap_exn place)
    ;

    value wrap2 place f = fun a b ->
      catch (fun () -> f a b)
      (wrap_exn place)
    ;

    value wrap4 place f = fun a b c d ->
      catch (fun () -> f a b c d)
      (wrap_exn place)
    ;

    value read_into = wrap4 "read_into" Lwt_io.read_into;

    value error = Lwt.fail;

    type output_channel = Lwt_io.output_channel;
    value stdout = Lwt_io.stdout;
    value write = wrap2 "write" Lwt_io.write;

    type input_channel = Lwt_io.input_channel;

    value open_in = wrap1 "open_in" (
      fun fn ->
        Lwt_io.open_file
          ~mode:Lwt_io.input
          ~flags:[Unix.O_RDONLY]
         fn
      )
    ;

    value close_in = wrap1 "close_in" Lwt_io.close;

    value runIO x : res 'a =
      try `Ok (Lwt_main.run x)
      with [e -> `Error e]
    ;

    value with_file_in_bin filename func =
      Lwt_io.with_file ~mode:Lwt_io.input filename func
    ;

    value with_file_out_bin filename func =
      Lwt_io.with_file ~mode:Lwt_io.output filename func
    ;

  end
;

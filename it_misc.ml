open It_Ops
;

module S = Subarray
;


module Js_escape(IO : It_Types.MonadIO)
 :
  sig
    exception Js_bad_escape of string;

    value unescape : (Iteratees.Make(IO)).enumeratee char char 'a;

    module I : sig exception Iteratees_err_msg of exn; end;
  end
 =
  struct

    exception Js_bad_escape of string;

    module I = Iteratees.Make(IO);

    open I;

    value it_bad_esc fmt = Printf.ksprintf
      (fun s -> throw_err (Js_bad_escape s)) fmt
    ;

    value it_hex exp_chars =
      joinI (limit exp_chars
        (gather_to_string))
      >>= fun str ->
      let str_len = String.length str in
      if str_len <> exp_chars
      then
        it_bad_esc "expected hex of %i chars, found only %i chars"
          exp_chars str_len
      else
        match
          (try Scanf.sscanf str "%x%!" (fun n -> Some n)
           with [ _ -> None ])
        with
        [ None -> it_bad_esc "expected hex number, found %S" str
        | Some n -> return n
        ]
    ;

    value unescape_utf16 : enumeratee char utf16item 'a = fun it ->
      let rec unescape_utf16 (it : iteratee int 'a) =
        break_feed ((=) '%') gather_to_string >>= fun it_str ->
        (joinI & return it_str) >>= fun str ->
        let it = feed_it
          it
          (let arr = Array.init
             (String.length str) (fun i -> Char.code str.[i]) in
           Chunk (S.of_array arr)
          ) in
        get_stream_eof >>= fun opt_opt_err ->
        match opt_opt_err with
        [ Some None -> return it
        | Some (Some err) -> throw_err err
        | None ->
            match it with
            [ IE_done _ | IE_cont (Some _) _ -> return it
            | IE_cont None k ->
                junk (* '%' *) >>= fun () ->
                peek >>= fun opt_c ->
                match opt_c with
                [ None -> it_bad_esc "eof after '%%'"
                | Some c ->
                    (if c = 'u' || c = 'U'
                     then
                       junk >>= fun () ->
                       it_hex 4
                     else
                       it_hex 2
                    ) >>= fun code ->
                    let it =
                      liftI
                        ( (k (chunk_of code)) >>% fun (it, _sl) ->
                          IO.return it
                        )
                    in
                      unescape_utf16 it
                ]
            ]
        ]
      in
        unescape_utf16 it
    ;


    value unescape_unicode it = joinI & unescape_utf16 (UTF8.utf8_of_utf16 it)
    ;

    value unescape it = joinI & unescape_unicode (UTF8.char_of_utf8 it)
    ;

  end
;











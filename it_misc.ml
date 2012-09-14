open It_Ops
;

module S = Subarray
;


module Subarray_cat
 :
  sig
    type t 'a;
    value make : list (Subarray.t 'a) -> t 'a;
    value length : t 'a -> int;
    value get : t 'a -> int -> 'a;
    value sub_copy_out : t 'a -> ~ofs:int -> ~len:int -> Subarray.t 'a;
  end
 =
  struct

    type t 'a = array (Subarray.t 'a)
    ;

    open It_Ops
    ;

    value make lst = Array.of_list &
      List.filter (fun s -> S.length s <> 0) lst
    ;

    value length sc =
      Array.fold_left (fun acc s -> acc + S.length s) 0 sc
    ;

    value outof () = invalid_arg "Subarray_cat.get"
    ;

    value get sc i =
      if i < 0
      then outof ()
      else
        let sc_len = Array.length sc in
        inner ~i ~j:0
        where rec inner ~i ~j =
          if j = sc_len
          then outof ()
          else
            let sj = sc.(j) in
            let sj_len = S.length sj in
            if i < sj_len
            then
              S.get sj i
            else
              inner ~i:(i - sj_len) ~j:(j+1)
    ;

    value sub_copy_out sc ~ofs ~len =
      let sc_len = length sc in
      if ofs < 0 || len < 0 || ofs+len > sc_len
      then invalid_arg "Subarray_cat.sub_copy_out"
      else
      S.of_array & Array.init len (fun i -> get sc (ofs+i))
    ;

  end
;


type uchar = int;


module UTF8(IO : It_Types.MonadIO)
 :
  sig
    value utf8_of_char : (Iteratees.Make(IO)).enumeratee char uchar 'a;
  end
 =
  struct

    open Iteratees;
    module I = Make(IO);
    open I;

    module SC = Subarray_cat;

    exception Bad_utf8 of string
    ;

(*  without actual conversion:
    value sc_ulen sc =
      let len = SC.length sc in
      (len, len, None)
    ;
    value sc_recode ~scfrom ~arrto ~uchars =
      for i = 0 to uchars-1 do
      ( arrto.(i) := Char.code & SC.get scfrom i
      )
      done
    ;
*)

    value relaxed_utf8 = ref False  (* TODO: check it. *)
    ;


    value in_tail byte =
      byte land 0b11_000_000 = 0b10_000_000

    and bad_tail =
      some & Bad_utf8 "tail != 0x80..0xBF"
    ;


    value decode_4bytes a b c d =
      ((a land 0b00_000_111) lsl 18) lor
      ((b land 0b00_111_111) lsl 12) lor
      ((c land 0b00_111_111) lsl 6) lor
      (d land 0b00_111_111)
    ;


    (* returns (count_of_chars, length_in_bytes, option error) *)
    value (sc_ulen : SC.t char -> (int * int * option exn)) sc =
      let sc_len = SC.length sc in
      let get i = Char.code (SC.get sc i) in
      let rec loop ~ch ~i =
        if i = sc_len
        then
          (ch, i, None)
        else
          let byte = get i in
          if byte < 0x80
          then loop ~ch:(ch+1) ~i:(i+1)
          else if byte <= 0xBF
          then (ch, i, some & Bad_utf8 "head 0x80..0xBF")
          else if byte <= 0xC1
          then
            (if relaxed_utf8.val
             then skip_tail ~ch ~i ~sz:2
             else (ch, i, some & Bad_utf8 "head 0xC0..0xC1 (overlong)")
            )
          else if byte < 0xE0
          then skip_tail ~ch ~i ~sz:2
          else if byte < 0xF0
          then skip_tail ~ch ~i ~sz:3
          else if byte <= 0xF4
          then skip_tail ~ch ~i ~sz:4
          else (ch, i, some & Bad_utf8 "head 0xF5..0xFF")
      and skip_tail ~ch ~sz ~i =  (* check len, then check_tail *)
        if i + sz > sc_len
        then (ch, i, None)
        else
          (if sz = 4 && not relaxed_utf8.val
           then check_tail4  (* check for codepoint too *)
           else check_tail ~len:(sz-1)
          ) ~i ~ch ~ifrom:(i+1)
      and check_tail ~i ~ch ~ifrom ~len =  (* just check for 0b10xxxxxx *)
        if len = 0
        then loop ~ch:(ch+1) ~i:ifrom
        else
          let byte = get ifrom in
          if in_tail byte
          then check_tail ~i ~ch ~ifrom:(ifrom+1) ~len:(len-1)
          else (ch, i, bad_tail)
      and check_tail4 ~i ~ch ~ifrom =  (* 0b10xxxxxx and codepoint *)
        let a = get i and b = get (i+1) and c = get (i+2) and d = get (i+3) in
        if not (in_tail b && in_tail c && in_tail d)
        then
          (ch, i, bad_tail)
        else
          let codepoint = decode_4bytes a b c d in
          if codepoint > 0x10FFFF
          then (ch, i, some & Bad_utf8 "codepoint > 0x10FFFF")
          else loop ~ch:(ch+1) ~i:(ifrom+4)
      in
        loop ~ch:0 ~i:0
    ;


    value sc_recode ~scfrom ~arrto ~uchars =
      let get i = Char.code (SC.get scfrom i) in
      let rec loop ~ifrom ~ito =
        if ito = uchars
        then ()
        else
          let a = get ifrom in
          if a < 0x80
          then put ~i:(ifrom+1) ~ito ~char:a
          else if a < 0xC0
          then assert False  (* sc_ulen checks this *)
          else
          let b = get (ifrom+1) in
          if a < 0xE0
          then
            put ~i:(ifrom+2) ~ito ~char:(
              ((a land     0b11_111) lsl 6) lor
              ( b land 0b00_111_111)
            )
          else
          let c = get (ifrom+2) in
          if a < 0xF0
          then
            put ~i:(ifrom+3) ~ito ~char:(
              ((a land      0b1_111) lsl 12) lor
              ((b land 0b00_111_111) lsl  6) lor
              ( c land 0b00_111_111)
            )
          else
          let d = get (ifrom+3) in
          put ~i:(ifrom+4) ~ito ~char:(decode_4bytes a b c d)

      and put ~i ~ito ~char =
        ( arrto.(ito) := char
        ; loop ~ifrom:i ~ito:(ito+1)
        )
      in
        loop ~ifrom:0 ~ito:0
    ;


    value ensure_size array_option_ref size =
      let realloc () =
        let r = Array.make size (-1) in
        ( array_option_ref.val := Some r
        ; r
        )
      in
      match array_option_ref.val with
      [ None -> realloc ()
      | Some array ->
          if Array.length array < size
          then realloc ()
          else
            (* for debugging: *)
            let () = Array.fill array 0 (Array.length array) (-2) in
            array
      ]
    ;

    value utf8_of_char uit =
      let arr_ref = ref None in
      let rec utf8_of_char ~acc uit =
        match uit with
        [ IE_cont None k -> ie_cont & fun s -> step ~acc ~k s
        | IE_cont (Some _) _ | IE_done _ -> return uit
        ]
      and step ~acc ~k stream =
        let err oe =
          k (EOF oe) >>% fun (iv, _s) ->
          IO.return (return iv, Sl.one stream)
        in
        match (acc, stream) with
        [ (`Error e, _) ->
            (* TODO: test this branch. *)
            (* let () = Printf.eprintf "utf8: (`Error, _)\n%!" in *)
            err & Some e
        | (_, EOF oe) ->
            (* mprintf "utf8: (_, `EOF None=%b)\n%!" (oe=None) >>% fun () -> *)
            err oe
        | (`Acc acc, Chunk c) ->
            let sc = SC.make [acc; c] in
            let (ulen_chars, ulen_bytes, error_opt) = sc_ulen sc in
            let res_arr = ensure_size arr_ref ulen_chars in
            let () = sc_recode ~scfrom:sc ~arrto:res_arr ~uchars:ulen_chars in
            k (Chunk (S.of_array_sub res_arr 0 ulen_chars)) >>% fun (iv, _) ->
            let acc' = match error_opt with
              [ None -> `Acc (SC.sub_copy_out sc ~ofs:ulen_bytes
                              ~len:(SC.length sc - ulen_bytes)
                             )
              | Some e -> `Error e
              ]
            in
            IO.return (utf8_of_char ~acc:acc' iv, Sl.empty)
        ]
      in
        utf8_of_char ~acc:(`Acc S.empty) uit
    ;

  end
;


module Js_escape(IO : It_Types.MonadIO)
 :
  sig
    exception Js_bad_escape of string;

    value unescape : (Iteratees.Make(IO)).enumeratee char uchar 'a;

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


    value unescape it = joinI & unescape_utf16 (UTF8.utf8_of_utf16 it)
    ;

  end
;











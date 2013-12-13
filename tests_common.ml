open It_Ops
;

open It_Types
;

(*
module IO = Direct_IO
;
*)

open Iteratees
;

module Tests_functor(IO : MonadIO)
=
struct

value dbg fmt = Printf.ksprintf (Printf.printf "%s\n%!") fmt
;

value runIO = IO.runIO
;

module P = Printf;
value sprintf fmt = P.sprintf fmt;
value () = P.printf "before functor app\n%!";

module I = Make(IO);
value () = P.printf "after functor app\n%!";
open I;

module Je = It_misc.Js_escape(IO);

value mprintf fmt =
  Printf.ksprintf
    (fun s ->
       IO.catch
         (fun () -> mprintf "%s" s)
         (fun
          [ Pure_IO.Pure "write" ->
              ( Printf.printf "%s%!" s ; IO.return () )
         | e -> IO.error e
         ]
         )
    )
    fmt
;


(* Primitive Tests *)

value () =
  Iteratees.enum_fd_buffer_size.val := 5
  (* for tests; in real life, there should be 1024 or so *)
;

value test_iteratee : iteratee char (char * char) =
   drop 1 >>= fun () ->
   head >>= fun v1 ->
   drop 2 >>= fun () ->
   head >>= fun v2 ->
   return (v1, v2)
;


value string_of_e e =
  let (e, p) =
    match e with
    [ Iteratees_err_msg e | Je.I.Iteratees_err_msg e -> (e, "")
    | EIO (e, p) -> (e, p)
    | e -> (e, "")
    ]
  in
  sprintf "error: %s%s\n"
    (Printexc.to_string e)
    (if p = "" then "" else sprintf " (at %S)" p)
;


value print_res f r =
  match r with
  [ `Ok v -> P.printf "res: ok: %s\n" (f v)
  | `Error e -> P.printf "%s\n" & string_of_e e
  ]
;

value print_char_tuple (c1, c2) = sprintf "(%C, %C)" c1 c2
;

value (runA : IO.m (iteratee 'el 'a) -> res 'a) i =
      let r = runIO (i >>% run) in (flush stdout; r)
;

value run_print f i =
  let r = runA i
  in
    print_res f r
;

value expl s =
  inner [] (String.length s - 1)
  where rec inner acc i =
    if i < 0
    then acc
    else inner [s.[i] :: acc] (i-1)
;

value test12 n =
  let i = enum_pure_nchunk (expl "abcde") n test_iteratee
  and pr = print_char_tuple in
  run_print pr i
;

value test3 () =
  let i = enum_pure_nchunk (expl "abc") 2 test_iteratee >>%
          enum_pure_nchunk (expl "de") 1
  and pr = print_char_tuple in
  run_print pr i
;


module H = Iteratees_http.It_http(IO)
;

(* Pure tests, requiring no IO *)

value test_str1 = expl &
    "header1: v1\rheader2: v2\r\nheader3: v3\nheader4: v4\n" ^
    "header5: v5\r\nheader6: v6\r\nheader7: v7\r\n\nrest\n"
;

value read_lines_and_one_more_line : iteratee 'a 'b =
  joinI (H.enum_lines stream2list) >>= fun lines ->
  H.line >>= fun after ->
  return (lines,after)
;


value with_err iter =
  iter >>= fun v ->
  is_stream_finished >>= fun e ->
  return (v, e)
;


value testp12 enum =
  let res = runA &
    enum read_lines_and_one_more_line
  in
  match res with
  [ `Error e -> failwith & string_of_e e
  | `Ok (lines, rest) ->
       ( assert (lines =
           [ "header1: v1"; "header2: v2"; "header3: v3"; "header4: v4"
           ; "header5: v5"; "header6: v6"; "header7: v7"
           ])
       ; assert (rest = (`Term, "rest"))
       )
  ]
;


value testp1 () = testp12 (enum_pure_1chunk test_str1)
;

value testp2 () = testp12 (enum_pure_nchunk test_str1 5)
;

value testw1 () =
  let test_str = expl "header1: v1\rheader2: v2\r\nheader3:\t v3"
  and expected = ["header1:"; "v1"; "header2:"; "v2"; "header3:"; "v3"] in
  let run_test test_str = runA &
     (enum_pure_nchunk test_str 5)
       (joinI (enum_words stream2list))
  in
  (
    print_res (String.concat (String.make 1 '|' (* to rewrite back*) )
                % List.map (sprintf "%S")
              )
    & run_test test_str
  ;
    assert (
         run_test test_str = `Ok expected
    )
  ; assert (
         run_test (List.append test_str [' ']) = `Ok expected
    )
   )
;


value (print_headers : list string -> IO.m unit) h =
  io_iter (fun i -> mprintf "header: %S\n" i >>% fun () -> IO.return ()) h
;


value string_of_termline (t, l) =
  sprintf "%S(%s)" l
    (match t with [ `Term -> "terminated" | `No_term -> "non-terminated" ])
;


(* + *)
(*
value () =
let line_collector = stream2list
in
  let read_lines_and_one_more_line
  : iteratee char ((list string * 'a) * ('b * string)) =
    joinI (enum_lines line_collector) >>= fun lines ->
let () = dbg "rl: lines got\n" in
    is_stream_finished >>= fun e ->
let () = dbg "rl: e got\n" in
    line >>= fun after ->
let () = dbg "rl: rest got\n" in
    return ((lines, e), after)
  in
  let (r : res _) =
  runIO
  (
    runA (
    enum_file "NUL" & read_lines_and_one_more_line
      )
  )
  in
  match r with
  [ `Ok _ -> printf "ok\n"
  | `Error ep -> printf "error: %s\n" & string_of_ep ep
  ]
;
value () = exit 0;
*)


(* Test Fd driver *)

value test_driver (line_collector : iteratee H.line 'a) filepath : IO.m unit
 =
  let read_lines_and_one_more_line : iteratee char 'y =
    joinI (H.enum_lines line_collector) >>= fun lines ->
    is_stream_finished >>= fun e ->
    H.line >>= fun after ->
    return ((lines, e), after)
  in
  mprintf "Opening file %S\n" filepath >>% fun () ->
  IO.open_in filepath >>% fun inch ->
  mprintf "About to read headers\n" >>% fun () ->
  mres (run %<< enum_fd inch read_lines_and_one_more_line) >>% fun result ->
  IO.close_in inch >>% fun () ->
  mprintf "Closed file %S\n" filepath >>% fun () ->
  mprintf "Finished reading headers\n" >>% fun () ->
  match result with
  [ `Ok ((_headers, None), after) ->
      mprintf "The line after headers is: %s\n"
        (string_of_termline after) >>% fun () ->
      mprintf "Complete headers.\n" >>% fun () ->
      IO.return ()
  | `Ok ((_headers, Some e), _after) ->
      mprintf "Problem: %s\n" (Printexc.to_string e) >>% fun () ->
      mprintf "Incomplete headers.\n" >>% fun () ->
      IO.return ()
  | `Error e ->
      mprintf "enumerator's error: %s\n" (string_of_e e) >>% fun () ->
      IO.error e
  ]
;


value dev_null = if Sys.os_type = "Win32" then "NUL" else "/dev/null";


value tests_driver () =
  let p i = ignore ((runIO & i) : res unit) in
  (
    (* Complete headers, up to "header7: v7" *)
    p & test_driver stream2list "test-files/test1.txt"

    (* The same *)
  ; p & test_driver stream2list "test-files/test2.txt"

    (* "header3: v3", then EOF *)
  ; p & test_driver stream2list "test-files/test3.txt"

    (* Incomplete headers [], EOF *)
  ; p & test_driver stream2list dev_null

  ; p & test_driver H.print_lines "test-files/test1.txt"
  ; p & test_driver H.print_lines "test-files/test2.txt"
  ; p & test_driver H.print_lines "test-files/test3.txt"
  ; p & test_driver H.print_lines dev_null
  )
;

           
(* Run the complete test, reading the headers and the body *)

(* This simple iteratee is used to process a variety of streams:
   embedded, interleaved, etc.
*)

(* +
   Don't know why, but there is no "joinI" in original sources.
*)

value line_printer : iteratee char unit =
  joinI & H.enum_lines H.print_lines
;


(* Two sample processors *)

(* Read the headers, print the headers, read the lines of the chunk-encoded
   body and print each line as it has been read
*)

value read_headers_print_body : iteratee char unit =
  (with_err & joinI & H.enum_lines stream2list) >>= fun headers'err ->
  (match headers'err with
   [ (headers, None) -> lift &
      mprintf "Complete headers\n" >>% fun () ->
      print_headers headers
   | (headers, Some e) -> lift &
      mprintf "Incomplete headers due to %s\n" (Printexc.to_string e)
        >>% fun () ->
      print_headers headers
   ]) >>= fun () ->
   (lift%mprintf) "\nLines of the body follow:\n" >>= fun () ->
   joinI & H.enum_chunk_decoded line_printer
;


(* Read the headers and print the header right after it has been read
   Read the lines of the chunk-encoded body and print each line as
   it has been read.
*)

(* +
   "()"-argument is here to suppress printing before actual call.
*)

value print_headers_print_body () : iteratee 'a unit =
  (lift%mprintf) "\nLines of the headers follow:\n" >>= fun () ->
  line_printer >>= fun () ->
  (lift%mprintf) "\nLines of the body follow:\n" >>= fun () ->
  joinI & H.enum_chunk_decoded line_printer
;


value test_driver_full iter filepath =
  mprintf "test_driver_full: %S\n" filepath >>% fun () ->
  IO.open_in filepath >>% fun inch ->
  mprintf "About to read headers\n" >>% fun () ->
  run %<< enum_fd inch iter >>% fun () ->
  IO.close_in inch >>% fun () ->
  mprintf "Finished reading\n"
;


value print_unit_res r =
  match r with
  [ `Ok () -> P.printf "ok.\n"
  | `Error e -> P.printf "%s\n" & string_of_e e
  ]
;


value tests_driver_full () =
  let p i = print_unit_res & runIO & i in
  ( ()

  ; p & test_driver_full read_headers_print_body "test-files/test_full1.txt"
    (*
       Complete headers
       ["header1: v1","header2: v2","header3: v3","header4: v4"]
       Problem Just "EOF"
       Incomplete body
       ["body line 1","body line    2","body line       3","body line          4"]
    *)
    (* +
       my observations: test_full1.txt has unfinished "body line 5",
       so it is reported (and should be reported) as "non-terminated
       body line 5".  This differs from Oleg's picture.
    *)

  ; p & test_driver_full read_headers_print_body "test-files/test_full2.txt"
    (* Exception: control message: Just Chunk decoding exc: Frame error *)

  ; p & test_driver_full read_headers_print_body "test-files/test_full3.txt"
    (* Complete headers
       ["header1: v1","header2: v2","header3: v3","header4: v4"]
       Problem Just "EOF"
       Incomplete body
       ["body line 1","body line    2","body line       3"
       ,"body line          4","body line             5"]
     *)

  ; p & test_driver_full (print_headers_print_body ())
          "test-files/test_full3.txt"

  )
;


(* +
   This is my test for enumeratee that transforms iteratee over
   utf8 chars (type [I.UTF8.uchar]) to iteratee over octets (type [char]).
*)

module U = I.UTF8;

value (dump_utf8_chars : iteratee uchar unit) =
(*
 let pr s = IO.catch
   (fun () -> mprintf "dump_utf8_chars: %s\n" s)
   (fun _ ->
      ( Printf.printf "direct output: dump_utf8_chars: %s\n%!" s
      ; IO.return ()
      )
   )
 in
*)
 ie_cont inner
 where rec inner s =
  match s with
  [ EOF opt_err ->
    let () = match opt_err with
      [ None -> dbg "natural end"
      | Some e -> dbg "unnatural end: \"%s\"" & Printexc.to_string e
      ]
      in
      match opt_err with
      [ None -> ie_doneM () s
      | Some e -> IO.return & (throw_err e, Sl.one s)
      ]
  | Chunk c ->
      let () = dbg "chunk of %i chars: [%s]"
        (S.length c)
        (String.concat "" &
         List.map (fun c -> sprintf "&#x%X;" (c : uchar :> int)) &
         S.to_list c)
      in
      ie_contM inner
  ]
;


value utf8_chars = expl "Мама мыла раму.  Qwert."
;

exception Myexc;

value test_utf8_enumeratee () =
(
  assert ((
    runA & enum_pure_nchunk utf8_chars 3
           (joinI & U.utf8_of_char dump_utf8_chars)
    ) = `Ok ()
  )
;
  let res =
      runA & (enum_pure_nchunk utf8_chars 3 >>> enum_err Myexc)
             (joinI & U.utf8_of_char dump_utf8_chars)
  in
(*
  match res with
  [ `Ok () -> assert False
  | `Error e -> P.printf "exn: %s\n%!" (Printexc.to_string e)
  ]
*)
    assert (res = `Error (Iteratees_err_msg Myexc))
;
  ()
)
;

value test_utf16_enumeratee () =
(
  dbg "test_utf16_enumeratee"
;
  assert ((
    runA & enum_pure_nchunk [0x41; 0x42; 0x0436; 0x43] 1
           (joinI & U.utf8_of_utf16 dump_utf8_chars)
    ) = `Ok ()
  )
;
  let res =
      runA & (enum_pure_nchunk [0x0436; 0xD834; 0xDF06; 0x0437] 1
              >>> enum_err Myexc)
             (joinI & U.utf8_of_utf16 dump_utf8_chars)
  in
(*
  match res with
  [ `Ok () -> assert False
  | `Error e -> P.printf "exn: %s\n%!" (Printexc.to_string e)
  ]
*)
    assert (res = `Error (Iteratees_err_msg Myexc))
;
  ()
)
;




value limit_chars = expl "12345678abcdefgh"
;


exception Bad_int of string
;


value limited_iteratee : iteratee char int =
  let is_digit = fun [ '0'..'9' -> True | _ -> False ] in
  break_chars (not % is_digit) >>= fun num_str ->
  try return & int_of_string num_str
  with [ Failure _ -> throw_err & Bad_int num_str ]
;


value test_limit ~feed_cont n =
 let () = P.printf "test_limit: n=%i, feed_cont=%b\n%!" n feed_cont in
 let ctch ~b itf =
   if not b
   then
     itf ()
   else
     catchk
      itf
      (fun err_msg _cont ->
         let () = P.printf "limited: caught %s%!" &
           match err_msg with
           [ Iteratees_err_msg e | e -> Printexc.to_string e ]
         in
           throw_err err_msg
      )
 in
 try
  let res = runA &
    (enum_pure_nchunk limit_chars 3)
    ( ctch ~b:True
        ( fun () ->
          (limit n limited_iteratee) >>= fun it ->
          ( match it with
            [ IE_done i -> return & Some i
            | IE_cont None cont ->
                let () = P.printf "limited: cont wants more data, %!" in
                if not feed_cont
                then
                  let () = P.printf "ignoring.\n%!" in
                  lift (cont (EOF None)) >>= fun _ ->
                  return None
                else
                  let () = P.printf "feeding.\n%!" in
                  ie_cont cont >>= fun i ->
                  return & Some i
            | IE_cont (Some e) _ ->
                let () = P.printf "limited: error: %s\n" & Printexc.to_string e
                in
                  return None
            ]) >>= fun oi ->
          break_chars (fun _ -> False) >>= fun str ->
          return (oi, str)
        )
    )
  in
  match res with
  [ `Ok (oi, str) ->
      P.printf "limited: i=%s str=%S\n\n%!"
        (match oi with
         [ None -> "None"
         | Some i -> string_of_int i
         ])
        str
  | `Error e -> P.printf "exn: %s\n\n%!" &
      match e with
      [ Iteratees_err_msg e | e -> Printexc.to_string e
      ]
  ]
 with
 [ e -> P.printf "ACHTUNG!  uncaught exn: %s\n%!" & Printexc.to_string e ]
;


(*

    ( ctch ~b:True
        ( fun () ->
          (joinI & limit n limited_iteratee) >>= fun i ->
          break_chars (fun _ -> False) >>= fun str ->
          return (i, str)
        )
    )

*)


value test_limits () =
  ( P.printf "\n%!"
  ; test_limit ~feed_cont:False 10
  ; test_limit ~feed_cont:False 5
  ; test_limit ~feed_cont:True 5
  )
;


value enum1 s i =
  match i with
  [ I.IE_cont None k -> k s >>% IO.return % fst
  | I.IE_cont (Some _) _ | I.IE_done _ -> IO.return i
  ]
;


value rec printexc e =
  match e with
  [ I.Iteratees_err_msg e -> printexc e
  | e -> Printexc.to_string e
  ]
;

value test_int32 (reader : I.iteratee char int32) string =
  let stream = I.Chunk (I.Subarray.of_string string) in
  let () = Printf.printf "%S -> %!" string in
  match IO.runIO ((enum1 stream reader) >>% I.run) with
  [ `Ok r -> Printf.printf "ok %li\n%!" r
  | `Error e -> Printf.printf "error \"%s\"\n%!"
      (printexc e)
  ]
;


value test_ints () =

  let max_int = Int64.of_int32 Int32.max_int in
  let pr = Printf.sprintf "%Li" in
  let samples_u =
    [ "0"
    ; "00"
    ; "123"
    ; "+123"
    ; "0123"
    ; "-123"
    ; pr max_int
    ; "000000" ^ pr max_int
    ; pr (Int64.add 1L max_int)
    ; pr (Int64.add 2L max_int)
    ; "19223372036854775806"
    ]
  in
  let samples = List.concat
    [ samples_u
    ; List.map (fun s -> "-" ^ s) samples_u
    ; List.map (fun s -> "+" ^ s) samples_u
    ]
  in
    ( P.printf "reading unsigned int32 with leading zeroes allowed:\n"
    ; List.iter (test_int32 read_uint32) samples
    ; print_newline ()
    ; P.printf "reading unsigned int32 with leading zeroes forbidden:\n"
    ; List.iter (test_int32 read_uint32_nz) samples
    ; print_newline ()

    ; P.printf "reading signed int32 with leading zeroes allowed:\n"
    ; List.iter (test_int32 read_int32) samples
    ; print_newline ()
    ; P.printf "reading signed int32 with leading zeroes forbidden:\n"
    ; List.iter (test_int32 read_int32_nz) samples
    ; print_newline ()
    )
;


value test_base64decode () =
  let cases =
    [ ("QWxhZGRpbjpvcGVuIHNlc2FtZQ==", "Aladdin:open sesame")
    ]
  and chunk_sizes = [1; 2; 3; 4; 5; 6; 10; 20; 100]
  and any_fail = ref False
  in
  let () =
    List.iter
      (fun chunk_size ->
         List.iter
           (fun (encoded, expected_decoded) ->
             let status =
             match IO.runIO
             (
              (enum_string ~chunk_size encoded)
              (I.base64_decode gather_to_string) >>% fun it ->
              I.run (joinI it)
             )
             with
             [ `Ok r ->
                 if expected_decoded = r
                 then `Ok
                 else `Error
                   (Printf.sprintf "doesn't match: expected %S, got %S"
                        expected_decoded r)
             | `Error e -> `Error (Printf.sprintf "error: %S" (printexc e))
             ]
             in
               match status with
               [ `Ok -> ()
               | `Error reason ->
                   ( any_fail.val := True
                   ; Printf.printf "(chunk %i) %S -> %s\n%!"
                       chunk_size encoded reason
                   )
               ]
           )
           cases
      )
      chunk_sizes
  in
    if any_fail.val
    then ()
    else Printf.printf "base64_decode tests ok\n%!"
;


(***********)

exception Left of (exn * string)
;


(*
value dump_after title =
   get_stream_eof >>= fun opt_opt_err ->
   let () = fdbg "after %s: %s"
     title
     (match opt_opt_err with
      [ None -> "some data"
      | Some None -> "usual EOF"
      | Some (Some e) ->
          Printf.sprintf "error: %s"
            (Printexc.to_string e)
      ]
     )
   in
     return ()
;
*)


value test_forms ~allsizes () =
  let test1 =
( "qwe\r\n-----------------------------7045176531256545735900303621\
\r\nContent-Disposition: form-data; name=\"MAX_FILE_SIZE\"\r\n\r\n100000\r\n\
-----------------------------7045176531256545735900303621\r\nContent-Disposit\
ion: form-data; name=\"uploadedfile\"; filename=\"allchars\"\r\nContent-Type: \
application/octet-stream\r\n\r\n\
\x00\x01\x02\x03\x04\x05\x06\x07\b\t\n\x0B\x0C\r\x0E\x0F\x10\x11\x12\x13\x14\
\x15\x16\x17\x18\x19\x1A\x1B\x1C\x1D\x1E\x1F !\"#$%&'()*+,-./0123456789:;<=>?\
@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~\x7F\x80\x81\
\x82\x83\x84\x85\x86\x87\x88\x89\x8A\x8B\x8C\x8D\x8E\x8F\x90\x91\x92\x93\x94\
\x95\x96\x97\x98\x99\x9A\x9B\x9C\x9D\x9E\x9F\xA0\xA1\xA2\xA3\xA4\xA5\xA6\xA7\
\xA8\xA9\xAA\xAB\xAC\xAD\xAE\xAF\xB0\xB1\xB2\xB3\xB4\xB5\xB6\xB7\xB8\xB9\xBA\
\xBB\xBC\xBD\xBE\xBF\xC0\xC1\xC2\xC3\xC4\xC5\xC6\xC7\xC8\xC9\xCA\xCB\xCC\xCD\
\xCE\xCF\xD0\xD1\xD2\xD3\xD4\xD5\xD6\xD7\xD8\xD9\xDA\xDB\xDC\xDD\xDE\xDF\xE0\
\xE1\xE2\xE3\xE4\xE5\xE6\xE7\xE8\xE9\xEA\xEB\xEC\xED\xEE\xEF\xF0\xF1\xF2\xF3\
\xF4\xF5\xF6\xF7\xF8\xF9\xFA\xFB\xFC\xFD\xFE\xFF\
\r\n-----------------------------7045176531256545735900303621--\r\n\
qwe"
, "-----------------------------7045176531256545735900303621"
, [ ( [ "Content-Disposition: form-data; name=\"MAX_FILE_SIZE\""
      ]
    , "100000"
    )
  ; ( [ "Content-Disposition: form-data; name=\"uploadedfile\"; file\
         name=\"allchars\""
      ; "Content-Type: application/octet-stream"
      ]
    , "\
\x00\x01\x02\x03\x04\x05\x06\x07\b\t\n\x0B\x0C\r\x0E\x0F\x10\x11\x12\x13\x14\
\x15\x16\x17\x18\x19\x1A\x1B\x1C\x1D\x1E\x1F !\"#$%&'()*+,-./0123456789:;<=>?\
@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~\x7F\x80\x81\
\x82\x83\x84\x85\x86\x87\x88\x89\x8A\x8B\x8C\x8D\x8E\x8F\x90\x91\x92\x93\x94\
\x95\x96\x97\x98\x99\x9A\x9B\x9C\x9D\x9E\x9F\xA0\xA1\xA2\xA3\xA4\xA5\xA6\xA7\
\xA8\xA9\xAA\xAB\xAC\xAD\xAE\xAF\xB0\xB1\xB2\xB3\xB4\xB5\xB6\xB7\xB8\xB9\xBA\
\xBB\xBC\xBD\xBE\xBF\xC0\xC1\xC2\xC3\xC4\xC5\xC6\xC7\xC8\xC9\xCA\xCB\xCC\xCD\
\xCE\xCF\xD0\xD1\xD2\xD3\xD4\xD5\xD6\xD7\xD8\xD9\xDA\xDB\xDC\xDD\xDE\xDF\xE0\
\xE1\xE2\xE3\xE4\xE5\xE6\xE7\xE8\xE9\xEA\xEB\xEC\xED\xEE\xEF\xF0\xF1\xF2\xF3\
\xF4\xF5\xF6\xF7\xF8\xF9\xFA\xFB\xFC\xFD\xFE\xFF\
"
    )
  ]
)
  in
    List.iter
      (fun (body, boundary, expected) ->
         let run_size sz =
           (* let () = fdbg "test_forms/run_size %i" sz in *)
           match IO.runIO
           ((enum_string ~chunk_size:sz
               body
               (     (H.it_multipart boundary
                        (fun headers ->
                           (* let () = fdbg "getting part" in *)
                           gather_to_string >>= fun part ->
                           (* let () = fdbg "got part (%i bytes): %S"
                             (String.length part) part in *)
                           (* dump_after "part" >>= fun () -> *)
                           return (headers, part)
                        )
                        (stream2list >>= fun lst ->
                         (* dump_after "all parts" >>= fun () -> *)
                         return lst
                        )
                     )
               )
            ) >>% run
           )
           with
           [ `Ok got ->
               if expected <> got
               then failwith "test failed"
               else Printf.printf "test passed\n%!"
           | `Error e ->
               failwith
                 (Printf.sprintf
                    "forms: test failed with exception: %s" (msg e)
                 )
               where rec msg e =
                 match e with
                 [ Left (e, s) ->
                     sprintf "%s (stream left: %S)"
                       (msg e) s
                 | H.Multipart_error s -> s
                 | Iteratees_err_msg e -> msg e
                 | e -> Printexc.to_string e
                 ]
           ]
         in
           if allsizes
           then
             ( for i = 1 to String.length body
               do
                 run_size i
               done
             )
           else
             run_size 617
      )
      [test1]
;


value string_hex_escape s =
  let b = Buffer.create 1 in
  loop 0
  where rec loop i =
    if i = String.length s
    then Buffer.contents b
    else
      let ch = s.[i] in
      let c = Char.code ch in
      let () =
        if c < 0x20 || c >= 0x80
        then Buffer.add_string b (Printf.sprintf "\\x%02X" c)
        else Buffer.add_char b ch
      in loop (i + 1)
;


value dump_chars : iteratee char unit =
  ie_cont step
  where rec step s =
    match s with
    [ EOF None -> ie_doneM (dbg "dump_chars: normal eof") s
    | EOF (Some e) -> ie_doneM (dbg "dump_chars: eof with error: %s"
        (Printexc.to_string e)) s
    | Chunk c ->
        let () = dbg "dump_chars: %s" (string_hex_escape & S.to_string c) in
        ie_contM step
    ]
;


value test_js_unescape () =
( dbg "test_js_unescape"
; assert ((
    runA & enum_pure_nchunk
           (expl "ab%2C*.cd%u0439%u0446%u0443ef%uD834%uDF06gh") 1
           (joinI & Je.unescape gather_to_string)
    ) = `Ok "ab,*.cd\xD0\xB9\xD1\x86\xD1\x83ef\xF0\x9D\x8C\x86gh"
  )
; dbg "passed"
)
;


value () =
  ( P.printf "TESTS BEGIN.\n"

  ; test12 5
  ; test12 2
  ; test3 ()
  ; testp1 ()
  ; testp2 ()

  ; testw1 ()

  ; tests_driver ()

  ; tests_driver_full ()

  ; test_utf8_enumeratee ()
  ; test_utf16_enumeratee ()

  ; test_limits ()

  ; test_ints ()

  ; test_base64decode ()

  ; test_forms ~allsizes:False ()

  ; test_js_unescape ()

  ; P.printf "TESTS END.\n"
  );

end;

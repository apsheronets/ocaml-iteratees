open Ops
;

open Types
;

module IO = Direct_IO
;

open Iteratees
;

module Tests_functor(IO : MonadIO)
=
struct

value runIO = IO.runIO
;

open Printf;
value () = printf "before functor app\n%!";
module I = Make(IO);
value () = printf "after functor app\n%!";

open I;


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
    [ Iteratees_err_msg e -> (e, "")
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
  [ `Ok v -> printf "res: ok: %s\n" (f v)
  | `Error e -> printf "%s\n" & string_of_e e
  ]
;

value print_char_tuple (c1, c2) = sprintf "(%C, %C)" c1 c2
;

value (runA : IO.m (iteratee 'el 'a) -> res 'a) i =
  runIO (i >>% run)
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

open H
;

(* Pure tests, requiring no IO *)

value test_str1 = expl &
    "header1: v1\rheader2: v2\r\nheader3: v3\nheader4: v4\n" ^
    "header5: v5\r\nheader6: v6\r\nheader7: v7\r\n\nrest\n"
;

value read_lines_and_one_more_line : iteratee 'a 'b =
  joinI (enum_lines stream2list) >>= fun lines ->
  line >>= fun after ->
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

value test_driver (line_collector : iteratee line 'a) filepath : IO.m unit
 =
  let read_lines_and_one_more_line : iteratee char 'y =
    joinI (enum_lines line_collector) >>= fun lines ->
    is_stream_finished >>= fun e ->
    line >>= fun after ->
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

  ; p & test_driver print_lines "test-files/test1.txt"
  ; p & test_driver print_lines "test-files/test2.txt"
  ; p & test_driver print_lines "test-files/test3.txt"
  ; p & test_driver print_lines dev_null
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
  joinI & enum_lines print_lines
;


(* Two sample processors *)

(* Read the headers, print the headers, read the lines of the chunk-encoded
   body and print each line as it has been read
*)

value read_headers_print_body : iteratee char unit =
  (with_err & joinI & enum_lines stream2list) >>= fun headers'err ->
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
   joinI & enum_chunk_decoded line_printer
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
  joinI & enum_chunk_decoded line_printer
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
  [ `Ok () -> printf "ok.\n"
  | `Error e -> printf "%s\n" & string_of_e e
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



value () =
  ( printf "TESTS BEGIN.\n"

  ; test12 5
  ; test12 2
  ; test3 ()
  ; testp1 ()
  ; testp2 ()

  ; testw1 ()

  ; tests_driver ()

  ; tests_driver_full ()

  ; printf "TESTS END.\n"
  );

end;

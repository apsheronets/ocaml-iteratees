open It_Types
;

open Dbg
;

open It_Ops
;

module It_http (IO : MonadIO)
 =
struct

open Iteratees
;

module I = Make(IO)
;

open I
;


(* Combining the primitive iteratees to solve the running problem:
   Reading headers and the content from an HTTP-like stream
*)

type line = string  (* The line of text, terminators are not included *)
;


(* Read the line of text from the stream
   The line can be terminated by CR, LF or CRLF.
   Return (Right Line) if successful. Return (Left Line) if EOF or
   a stream error were encountered before the terminator is seen.
   The returned line is the string read so far.
   This is a totally high-level Iteratee, built by composing low-level
   ones. It knows nothing about the representation of Iteratees.
*)

value (line : iteratee char ([= `No_term | `Term] * line)) =
  let lf = ['\n'] in
  let crlf = ['\r'; '\n'] in
  let check l ts =
    return & ((if ts = 0 then `No_term else `Term), l)
  in
  let terminators =
    heads crlf >>= fun n ->
    if n == 0
    then heads lf
    else return n
  in
    break_chars (fun c -> c == '\r' || c == '\n') >>= fun l ->
let () = dbg "http_line: %S\n" l in
    terminators >>= fun ts ->
    check l ts
;


(* Line iteratees: processors of a stream whose elements are made of Lines

   Print lines as they are received. This is the first `impure' iteratee
   with non-trivial actions during chunk processing
*)

value (print_lines : iteratee line unit) =
  let pr_line l = print_line (">> read line: " ^ l)
  in
  ie_cont step
  where rec step s =
    match s with
    [ Chunk c ->
        let lst = S.to_list c in
        if lst = []
        then ie_contM step
        else io_iter pr_line lst >>% fun () -> ie_contM step
    | EOF e ->
        pr_line
          (if e = None
           then ">> natural end"
           else ">> unnatural end"
          ) >>% fun () ->
        ie_doneM () s
    ]
;


(* Combining the primitive iteratees to solve the running problem:
   Reading headers and the content from an HTTP-like stream

   Convert the stream of characters to the stream of lines, and
   apply the given iteratee to enumerate the latter.
   The stream of lines is normally terminated by the empty line.
   When the stream of characters is terminated, the stream of lines
   is also terminated, abnormally.
   This is the first proper Enumeratee: it is the iteratee of the
   character stream and the enumerator of the line stream.
   More generally, we could have used sequence_stream to implement enum_lines.
*)

exception Non_terminated_lines
;

value rec (enum_lines : enumeratee char string 'a) i =
  match i with
  [ IE_cont None k ->
let () = dbg "enum_lines: IE_cont\n" in
      line >>= fun term_line ->
        match term_line with
        [ (`Term, "") ->
let () = dbg "enum_lines:   empty line\n" in
            return i  (* empty line, normal exit *)
        | (`Term, l) ->
let () = dbg "enum_lines:   term: %S\n" l in
            liftI (
            k (chunk_of l) >>% fun (i, _s) ->
            IO.return (enum_lines i)
            )
        | (`No_term, l) ->
let () = dbg "enum_lines:   non-term: %S\n" l in
            (lift : _)
            (k (if l="" then EOF (Some End_of_file) else chunk_of l)
             >>% fun (i, _s) ->
             enum_err End_of_file i
            )
        ]
  | IE_cont (Some _) _ ->
let () = dbg "enum_lines: error\n" in
      return i
  | IE_done _ ->
let () = dbg "enum_lines: done\n" in
      return i
  ]
;


(* HTTP chunk decoding
   Each chunk has the following format:

   	  <chunk-size> CRLF <chunk-data> CRLF
  
   where <chunk-size> is the hexadecimal number; <chunk-data> is a
   sequence of <chunk-size> bytes.
   The last chunk (so-called EOF chunk) has the format
   0 CRLF CRLF (where 0 is an ASCII zero, a character with the decimal code 48).
   For more detail, see "Chunked Transfer Coding", Sec 3.6.1 of
   the HTTP/1.1 standard:
   http://www.w3.org/Protocols/rfc2616/rfc2616-sec3.html#sec3.6.1

   The following enum_chunk_decoded has the signature of the enumerator
   of the nested (encapsulated and chunk-encoded) stream. It receives
   an iteratee for the embedded stream and returns the iteratee for
   the base, embedding stream. Thus what is an enumerator and what
   is an iteratee may be a matter of perspective.

   We have a decision to make: Suppose an iteratee has finished (either because
   it obtained all needed data or encountered an error that makes further
   processing meaningless). While skipping the rest of the stream/the trailer,
   we encountered a framing error (e.g., missing CRLF after chunk data).
   What do we do? We chose to disregard the latter problem.
   Rationale: when the iteratee has finished, we are in the process
   of skipping up to the EOF (draining the source).
   Disregarding the errors seems OK then.
   Also, the iteratee may have found an error and decided to abort further
   processing. Flushing the remainder of the input is reasonable then.
   One can make a different choice...
*)

exception EChunked of string;

value (enum_chunk_decoded : enumeratee char char 'a) iter =
  let rec (enum_chunk_decoded : enumeratee char char 'a) iter =
    break_chars ( (=) '\r') >>= fun size_str ->
    match size_str with
    [ "" -> frame_err (exc "Error reading chunk size") iter
    | str ->  (* todo: ptso *)
        match read_hex str with
        [ None -> frame_err (exc ("Bad chunk size: " ^ str)) iter
        | Some size ->
            let () = dbg "enum_chunk_decoded: frame %i (%x) bytes\n" size size in
            getCRLF iter (
            take size iter >>= fun r ->
            getCRLF r (
            if size = 0
            then return r
            else enum_chunk_decoded r
            ))
        ]
    ]

  and getCRLF iter m =
    heads ['\r'; '\n'] >>= fun n ->
    if n = 2
    then m
    else frame_err (exc "Bad Chunk: no CRLF") iter

  and read_hex x =
    try Scanf.sscanf x "%x%!" (fun i -> Some i)
    with [ Scanf.Scan_failure _ -> None ]

  and exc msg = EChunked msg

  (* If the processing is restarted, we report the frame error to the inner
    Iteratee, and exit
  *)
  and frame_err e iter =
    throw_recoverable_err (exc "Frame error")
    (fun s -> enum_err e iter >>% fun i -> IO.return (return i, Sl.one s))
  in
    enum_chunk_decoded iter
;

end;

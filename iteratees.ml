(* 34567890123456789 1234567890123456789 1234567890123456789 1234567890123456 *)

(* todo: string_of_*err* -- вытащить так, чтобы wrapped-exns учитывались. *)
(* todo: разбить на файлы. *)

(* +
   The comments in this source are taken from original source file
   ( http://okmij.org/ftp/Haskell/Iteratee/IterateeM.hs ),
   except for comments that have "+" sign in first line (like this comment).
   Comments with "+" were added by Dmitry Grebeniuk (gdsfh1 at gmail dot com),
   who have ported Iteratees to OCaml.
*)

(* +
   If you are using "=<<" or "%<<" infix operators, and they will probably
   occur in some commented code.  Preprocessor will treat "<<" in comments
   as the beginning of quotation.  The best way to deal with it is to add
   "-no_quot" to your preprocessor's command line:
   -pp "camlp4 your_pp_modules" => -pp "camlp4 -no_quot your_pp_modules"
   or add ocamlbuild's "camlp4:no_quot" tag to some files
   (target "your_file.ml") or all your ml- and mli-files
   (target <*.ml> | <*.mli>).  (see for example "_tags" in this library.)
*)

value enum_fd_buffer_size = ref 4096
;

value break_chars_buf_init_size = 25
;

open Ops
;

open Dbg
;

module S = Subarray
;

open Types
;

(* +
   In OCaml, Iteratees' [err_msg] is represented by simple exception.
   [err_msg] can be Iteratees' internal exception, user-defined Iteratees'
   exception, or an IO exception, wrapped into [EIO] exception.

   IO errors (see MonadIO signature) carry the tuple of exception and
   the place where exception was raised (similar to
   [Unix.Unix_error (error, place, argument)] exception; I find it useful).

   Sometimes we need to wrap Iteratees' error into IO error:
   [Iteratees_err_msg err_msg] represents such wrapped exception.

   Functions [merr_of_ierr] (IO-monad error of Iteratees' error) and
   [ierr_of_merr] know about wrapping, and they unwrap such exceptions.
*)

type err_msg = exn;
exception EIO of (exn * place);
exception Iteratees_err_msg of err_msg;


(* +
   Some iteratees do not follow conventions described by Oleg
   (not every iteratee is `good').  When library founds that
   iteratee is `bad', the exception [Divergent_iteratee place]
   is the result of computation.  [place] is the name of function
   that found that iteratee is `bad', sometimes it's useful for
   debugging.
*)

exception Divergent_iteratee of place;


(* +
   Function [merr_of_ierr] implemented inside functor, since
   it depends on [IO.error] to return the value of [IO.m 'a] type.
*)

value ierr_of_merr (ep : (exn * place)) : err_msg =
  match ep with
  [ (Iteratees_err_msg e, _) -> e
  | ep -> EIO ep
  ]
;


(* A stream is a (continuing) sequence of elements bundled in Chunks.
   The first variant means no more data will be coming: the stream
   is exhausted, either due to EOF or some error.
   Chunk [a] gives the currently available part of the stream.
   The stream is not terminated yet.
   The case (Chunk []) signifies a stream with no currently available
   data but which is still continuing. A stream processor should,
   informally speaking, ``suspend itself'' and wait for more data
   to arrive.
*)

type stream 'el =
  [ EOF of option err_msg
  | Chunk of S.t 'el
  ]
;

value chunk_of elem = Chunk (S.of_elem elem)
;


value dbgstream s =
  match s with
  [ EOF eopt ->
      Printf.sprintf "s:EOF{e=%s}" &
      match eopt with
      [ None -> "None"
      | Some exn -> Printf.sprintf "Some{%s}" & Printexc.to_string exn
      ]
  | Chunk b -> Printf.sprintf "s:Chunk{arr[%i],ofs=%i,len=%i}"
      (Array.length b.S.arr) b.S.ofs b.S.len
  ]
;


module Make (IO : MonadIO)
=
struct

value ( >>% ) m f = IO.bind f m;

(* +
   OCaml operators' priorities allow to use
   "  a          >>% fun _ ->
      f %<< m    >>% fun _ ->
      ..
   "
   without parenthesis around "f %<< m".
*)

value ( %<< ) = IO.bind;


(* Iteratee -- a generic stream processor, what is being folded over
   a stream
   This is the monadic version of Iteratee from Iteratee.hs
   + ported to OCaml +
   Please see the file Iteratee.hs for the discussion
   of design decisions.
   The basic design: Iteratee takes the chunk of the input stream and
   returns one of:
      -- the computed result and the remaining part of the stream.
         If the stream is finished (i.e., the EOF x is received), 
         that EOF value is returned as the  `remaining part of the stream';
      -- the indication that Iteratee needs more data, along
         with the continuation to process these data;
      -- a message to the stream producer (e.g., to rewind the stream)
         or an error indication.
   We assume that all iteratees are `good' -- given bounded input,
   they do the bounded amount of computation and take the bounded amount
   of resources.
   We also assume that given a terminated stream, an iteratee
   moves to the done state, so the results computed so far could be returned.
   The monad m describes the sort of computations done
   by the iteratee as it processes the stream. The monad m could be
   the identity monad (for pure computations) or the IO monad
   (to let the iteratee store the stream processing results as they
   are computed).
*)

type iteratee 'el 'a =
  [ IE_done of 'a
  | IE_cont of option err_msg
            and (stream 'el -> IO.m (iteratee 'el 'a  *  stream 'el))
  ]
;


(* It turns out, Iteratee forms a monad. *)

value return res = IE_done res
;


value rec
(bindI : ('a -> iteratee 'el 'b) -> iteratee 'el 'a -> iteratee 'el 'b)
f it =
  match it with
  [ IE_done a -> f a
  | IE_cont e k ->
      let docase it_s =
        match it_s with
        [ (IE_done a, stream) ->
            match f a with
            [
              IE_cont None m -> m stream
            | (IE_cont (Some _) _ | IE_done _) as i ->
                IO.return (i, stream)
            ]
        | (((IE_cont _) as i), s) -> IO.return (bindI f i, s)
        ]
      in
        IE_cont e (fun s -> (k s >>% docase))
  ]
;

value ( =<< ) = bindI
;

value ( >>= ) m f = bindI f m
;


value (lift : IO.m 'a -> iteratee 'el 'a) m =
  IE_cont None (fun s -> m >>% fun x -> IO.return (return x, s))
;


(* Throw an irrecoverable error *)

value rec throw_err e : iteratee 'el 'a =
  IE_cont (Some e) (fun s -> IO.return (throw_err e, s))
;


(* Throw a recoverable error *)

value throw_recoverable_err e cont : iteratee 'el 'a =
  IE_cont (Some e) cont
;


(* Produce the EOF error message to be passed to throwErr. 
   If the stream was terminated because of an error, keep the original 
   error message.
*)

value (set_eof : stream 'el -> err_msg) s =
  match s with
  [ EOF (Some e) -> e
  | EOF None | Chunk _ -> End_of_file
  ]
;


(* Useful combinators for implementing iteratees and enumerators *)

value empty_stream = Chunk S.empty
;


(* +
   [ie_doneM] and [ie_contM] are useful inside [IE_cont] continuation,
   they return from [IE_cont] either "iteratee returns [x] and maybe
   some data left in stream [s]", or "we have processed stream (1),
   but we have no result yet -- pass more data to the function [k]".
   "empty_stream" in ie_contM code is the reflection of fact (1).
*)

value ie_doneM x s = IO.return (IE_done x, s)
;

value ie_contM k = IO.return (IE_cont None k, empty_stream)
;


(* +
   Almost unusable in OCaml, since value monomorphism/restriction(?)
   for function applications (for [ie_cont some_cont]) bound to
   top-level values.  For top-level values, [IE_cont None some_cont]
   should be used instead.
*)

value (ie_cont : (stream 'el -> IO.m (iteratee 'el 'a * stream 'el)) ->
                 iteratee 'el 'a)
cont =
  IE_cont None cont
;


value (liftI : IO.m (iteratee 'el 'a) -> iteratee 'el 'a) m =
  ie_cont (fun s -> m >>% run' s)
  where run' s i =
    match i with
    [ IE_cont None k -> k s
    | IE_cont (Some _) _ | IE_done _ -> IO.return (i, s)
    ]
;


value merr_of_ierr (e : err_msg) : IO.m 'a =
  IO.error &
  match e with
  [ EIO ep -> ep
  | e -> (Iteratees_err_msg e, "")
  ]
;



(* The following is a `variant' of join in the Iteratee el m monad.
   When el' is the same as el, the type of joinI is indeed that of
   true monadic join. However, joinI is subtly different: since
   generally el' is different from el, it makes no sense to
   continue using the internal, Iteratee el' m a: we no longer
   have elements of the type el' to feed to that iteratee.
   We thus send EOF to the internal Iteratee and propagate its result.
   This join function is useful for Enumeratees, for embedded/nested streams. 
   For example, the common pattern is
     do
       lines <- joinI $ enum_lines stream2list
   The tests below show many examples (e.g., read_lines_and_one_more_line).
  
   joinI can be implemented as
     joinI outer = outer >>= lift . run
   The following is an optimized implementation, obtained by inlining.
*)

(* +
   And even more optimized and simplified version:
*)

value (joinI : iteratee 'el (iteratee 'el' 'a) -> iteratee 'el 'a)
outer_iter =
  outer_iter >>= fun inner_iter ->
  match inner_iter with
  [ IE_done inner_result -> return inner_result
  | IE_cont (Some e) _ -> throw_err e
  | IE_cont None inner_k ->
      ie_cont & fun outer_stream ->
      (inner_k (EOF None)) >>% fun (inner_iter2, _el'_stream) ->
      match inner_iter2 with
      [ IE_done inner_result -> ie_doneM inner_result outer_stream
      | IE_cont opt_err _inner_k2 ->
          match opt_err with
          [ Some e -> merr_of_ierr e
          | None -> IO.error (Divergent_iteratee "joinI", "")
          ]
      ]
  ]
;


(* Send EOF to Iteratee and disregard the unconsumed part of the stream
run' :: Monad m => Iteratee el m a -> m a
run' iter = check $ joinI (return iter)
 where
 check (IE_done x)   = return x
 check (IE_cont e _) = error $ "control message: " ++ show e

   The following is a more optimized implementation
*)

value (run : iteratee 'el 'a -> IO.m 'a) it =
  match it with
  [ IE_done a -> IO.return a
  | IE_cont (Some e) _ -> merr_of_ierr e
  | IE_cont None k ->
      k (EOF None) >>% fun (i, _s) ->
      match i with
      [ IE_done x -> IO.return x
      | IE_cont opt_exn _ ->
let () = dbg "run: exn=%s\n" &
  match opt_exn with
  [ None -> "none"
  | Some e -> Printexc.to_string e
  ]
in
          IO.error & match opt_exn with
          [ None -> (Divergent_iteratee "run", "run")
          | Some e -> (e, "")
          ]
      ]
  ]
;


(* Primitive iteratees *)

(* Read a stream to the end and return all of its elements as a list
   This primitive iteratee is quite useful when writing test cases.
*)

value (stream2list : iteratee 'el (list 'el)) =
  IE_cont None (fun s -> step [] s
    where rec step rev_acc s =
let () = dbg "s2l: step: acc=%i\n" & List.length rev_acc in
      match s with
      [ Chunk c ->
          if S.is_empty c
          then ie_contM (step rev_acc)
          else ie_contM (step (S.append_to_list_rev c rev_acc))
      | EOF _ as stream -> ie_doneM (List.rev rev_acc) stream
      ]
  )
;


(* Check if the stream is finished or harbors an error *)

value (is_stream_finished : iteratee 'el (option err_msg)) =
  IE_cont None (fun s ->
    match s with
    [ EOF opt_err_msg -> ie_doneM
        (if opt_err_msg = None
         then Some End_of_file
         else opt_err_msg
        )
        s
    | Chunk _ -> ie_doneM None s
    ]
  )
;


(* Primitive iteratees: parser combinators *)

(* The analogue of hs' List.break
   It takes an el predicate and returns a string of els,
   which is the (possibly empty) prefix of the stream. None of the
   characters in the string satisfy the el predicate.
   If the stream is not terminated, the first el of the remaining
   stream satisfies the predicate
*)

(* +
   Generalized to [break_fold].
*)

value (break_fold : ('el -> bool) -> ('a -> 'el -> 'a) -> 'a ->
                    iteratee 'el 'a ) cpred func init =
  IE_cont None
    (let rec step acc s =
       match s with
       [ Chunk c ->
           if S.is_empty c
           then ie_contM (step acc)
           else
             let (matches, tail) = S.break cpred c in
let () = dbg "S.break: %i -> %i+%i\n" (S.length c) (S.length matches) (S.length tail) in
             let new_acc = S.fold S.L func acc matches in
             if S.is_empty tail
             then ie_contM (step new_acc)
             else ie_doneM (new_acc) (Chunk tail)
       | EOF _  as e -> ie_doneM acc e
       ]
     in
       step init
    )
;


value (mapI : ('a -> 'b) -> iteratee 'el 'a -> iteratee 'el 'b) f i =
  i >>= return % f
;


value (break : ('el -> bool) -> iteratee 'el (list 'el)) cpred =
  mapI List.rev &
  break_fold cpred (fun acc elem -> [elem :: acc]) []
;


(* +
   [prepend f (fun x -> i)] returns an iteratee [ires]
   which behaves exactly as [i], but each time when [ires] begins
   to process data, [f ()] is called and its result is given to
   [fun x -> i] function.
*)

value (prepend : (unit -> 'x) -> ('x -> iteratee 'el 'a) -> iteratee 'el 'a)
f i =
  ie_cont & fun s ->
    match i (f ()) with
    [ IE_done x -> ie_doneM x s
    | IE_cont None k -> k s
    | IE_cont (Some e) _ -> merr_of_ierr e
    ]
;


value (break_chars : (char -> bool) -> iteratee char string) cpred =
  mapI (fun b ->
     let r = Buffer.contents b in (dbg "break_chars: b=%i, cont=%S\n"
       (Obj.magic b) r; r)
  ) &
  prepend
    (fun () -> Buffer.create break_chars_buf_init_size)
    (fun buf ->
       break_fold
         cpred
         (fun buf c -> (Buffer.add_char buf c; buf))
         buf
    )
;


(* A particular optimized case of the above: skip all elements of the stream
   satisfying the given predicate -- until the first element
   that does not satisfy the predicate, or the end of the stream.
   This is the analogue of hs' List.dropWhile
*)

value (drop_while : ('el -> bool) -> iteratee 'el unit) cpred =
  IE_cont None step
  where rec step s =
    match s with
    [ Chunk c ->
        let str = S.drop_while cpred c in
let () = dbg "drop_while: %i -> %i\n" (S.length c) (S.length str) in
        if S.is_empty str
        then ie_contM step
        else ie_doneM () (Chunk str)
    | EOF _ -> ie_doneM () s
    ]
;


(* Look ahead at the next element of the stream, without removing
   it from the stream.
   Return (Just c) if successful, return Nothing if the stream is
   terminated (by EOF or an error)
*)

value (peek : iteratee 'el (option 'el)) =
  IE_cont None
    (let rec step s =
       match s with
       [ Chunk c ->
           match S.get_first_item c with
           [ None -> ie_contM step
           | Some el -> ie_doneM (Some el) s
           ]
       | EOF _ -> ie_doneM None s
       ]
     in
       step
    )
;


(* Attempt to read the next element of the stream and return it.
   Raise a (recoverable) error if the stream is terminated
*)

value (head : iteratee 'el 'el) =
  IE_cont None step
  where rec step s =
    match s with
    [ Chunk c ->
        match S.destruct_first_item c with
        [ None -> ie_contM step
        | Some (h, t) -> ie_doneM h (Chunk t)
        ]
    | EOF _ -> IO.return (IE_cont (Some (set_eof s)) step, s)
    ]
;


value pervasives_eq x y = (0 = Pervasives.compare x y)
;


(* Given a sequence of elements, attempt to match them against
   the elements on the stream. Return the count of how many
   elements matched. The matched elements are removed from the
   stream.
   For example, if the stream contains "abd", then (heads "abc") 
   will remove the characters "ab" and return 2.
*)

value (heads : ?eq:('el->'el->bool) -> list 'el -> iteratee 'el int)
?(eq=pervasives_eq) str =
  let rec loop cnt str =
    if str = []
    then return cnt
    else ie_cont (fun s -> step cnt str s)
  and step cnt str s =
    match (str, s) with
    [ (_, EOF _) | ([], _) -> ie_doneM cnt s
    | ([strh :: strt], Chunk c) ->
        match S.destruct_first_item c with
        [ None -> ie_contM (step cnt str)
        | Some (h, t) ->
            if eq strh h
            then step (cnt + 1) strt (Chunk t)
            else ie_doneM cnt s
        ]
    ]
  in
    loop 0 str
;


(* Skip the rest of the stream *)

value (skip_till_eof : iteratee 'el unit) =
  IE_cont None step
  where rec step s =
    match s with
    [ Chunk _ -> ie_contM step
    | EOF _ -> ie_doneM () s
    ]
;


(* Skip n elements of the stream, if there are that many
   This is the analogue of hs' List.drop
*)

value (drop : int -> iteratee 'el unit) n =
  if n = 0
  then return ()
  else IE_cont None (step n)
    where rec step n s =
      match s with
      [ Chunk c ->
          let len = c.S.len in
          if len < n
          then ie_contM (step (n - len))
          else ie_doneM () (Chunk (S.drop n c))
      | EOF _ -> ie_doneM () s
      ]
;


value rec (io_iter : ('a -> IO.m unit) -> list 'a -> IO.m unit) f l =
  match l with
  [ [] -> IO.return ()
  | [h :: t] -> f h >>% fun () -> io_iter f t
  ]
;


value print_line s =
  IO.write IO.stdout (s ^ "\n")
;


(* Enumerators
   Each enumerator takes an iteratee and returns an iteratee:
   an Enumerator is an iteratee transformer.
   The enumerator normally stops when the stream is terminated
   or when the iteratee moves to the done state, whichever comes first.
*)

type enumerator 'el 'a = iteratee 'el 'a -> IO.m (iteratee 'el 'a);


(* It is typical for an enumerator to disregard the remaining-stream
   part of the state of the Iteratee computations. Some enumerators
   may use this remaining stream data to report a location of an error
   in stream terms, for example.
*)

(* The most primitive enumerator: applies the iteratee to the terminated
   stream. The result is the iteratee usually in the done state.
   A `good' iteratee must move to the done state or error state
   upon receiving the EOF.
*)

value (enum_eof : enumerator 'el 'a) i =
  match i with
  [ (IE_cont (Some _) _) | IE_done _ -> IO.return i
  | IE_cont None k ->
      k (EOF None) >>% fun (i, _s) ->
      IO.return &
      match i with
      [ IE_done _ -> i  (* done state *)
      | IE_cont None _ -> throw_err & Divergent_iteratee "enum_eof"
      | IE_cont (Some e) _ -> throw_err e   (* error state *)
      ]
  ]
;


(* Another primitive enumerator: tell the Iteratee the stream terminated
   with an error
*)

value (enum_err : err_msg -> enumerator 'el 'a) e i =
  match i with
  [ IE_cont None k -> k (EOF (Some e)) >>% fun (i, _s) ->
      IO.return &
      match i with
      [ IE_done _ -> i  (* done state *)
      | IE_cont None _ -> throw_err & Divergent_iteratee "enum_err"
      | IE_cont (Some e) _ -> throw_err e  (* error state *)
      ]
  | IE_done _ | IE_cont (Some _) _ -> IO.return i
  ]
;


(* The composition of two enumerators: just the functional composition.
   It is convenient to flip the order of the arguments of the composition
   though: in e1 >>> e2, e1 is executed first.
   The composition of enumerators is not exactly (.): we take care
   to force the result of the enumerator e1 before passing it to e2.
   We are thus certain that all effects of enumerating e1 happen before
   the effects of e2.
*)

value ( (>>>) : enumerator 'el 'a -> enumerator 'el 'a -> enumerator 'el 'a)
e1 e2 =
  fun i -> e1 i >>% e2
;


(* The pure 1-chunk enumerator
   It passes a given string to the iteratee in one chunk
   This enumerator does no IO and is useful for testing of base parsing
*)

value (enum_pure_1chunk : list 'el -> enumerator 'el 'a) lst i =
  let c = S.of_list lst in
  match i with
  [ IE_cont None k -> k (Chunk c) >>% IO.return % fst
  | IE_cont (Some _) _ | IE_done _ -> IO.return i
  ]
;


(* The pure n-chunk enumerator
   It passes a given string to the iteratee in chunks no larger than n.
   This enumerator does no IO and is useful for testing of base parsing
   and handling of chunk boundaries
*)

value (enum_pure_nchunk : list 'el -> int -> enumerator 'el 'a) lst n i =
  let rec loop str i =
    let ret () = IO.return i in
    if S.is_empty str
    then ret ()
    else
      match i with
      [ IE_cont None k ->
          let (s1, s2) = S.split_at n str in
          k (Chunk s1) >>% loop s2 % fst
      | IE_cont (Some _) _ | IE_done _ -> ret ()
      ]
  in
    loop (S.of_list lst) i
;


value mprintf fmt = Printf.ksprintf (IO.write IO.stdout) fmt
;


value (mres : IO.m 'a -> IO.m (res 'a)) m =
  IO.catch
    (fun () -> m >>% fun r -> IO.return & `Ok r)
    (fun ep -> IO.return & `Error ep)
;

value (_munres : res 'a -> IO.m 'a) r =
  match r with
  [ `Ok x -> IO.return x
  | `Error ep -> IO.error ep
  ]
;


(* The enumerator of M's channels
   We use the same buffer all throughout enumeration
*)

value (enum_fd : IO.input_channel -> enumerator char 'a) inch i =
  let buffer_size = enum_fd_buffer_size.val in
  let buf_str = String.create buffer_size
  and buf_arr = Array.make buffer_size '\x00' in
  let rec loop k =
    mres (IO.read_into inch buf_str 0 buffer_size) >>% fun read_res ->
    match read_res with
    [ `Error ep ->
        k (EOF (some & ierr_of_merr ep)) >>% IO.return % fst
    | `Ok have_read ->
        mprintf "Read buffer, size %i\n" have_read >>% fun () ->
        let () = assert (have_read >= 0) in
        if have_read = 0
        then
          IO.return (ie_cont k)
        else
          let c = S.replace_with_substring buf_arr buf_str 0 have_read in
          k (Chunk c) >>% check % fst
    ]
  and check i =
    match i with
    [ IE_cont None k -> loop k
    | IE_cont (Some _) _ | IE_done _ -> IO.return i
    ]
  in
    check i
;


value (enum_file : string -> enumerator char 'a) filepath iterv =
  mprintf "opened file %S\n" filepath >>% fun () ->
  IO.open_in filepath >>% fun inch ->
  enum_fd inch iterv >>% fun r ->
  IO.close_in inch >>% fun () ->
  mprintf "closed file %S\n" filepath >>% fun () ->
  IO.return r
;



(* Stream adapters: Iteratees and Enumerators at the same time *)

(* Stream adapters, or Enumeratees, handle nested streams. Stream nesting, 
   or encapsulation, is rather common: buffering, character encoding, 
   compression, encryption, SSL are all examples of stream nesting. On one
   hand, an Enumeratee is an Enumerator of a nested stream:
   it takes an iteratee for a nested stream, feeds its some data,
   returning the resulting iteratee when the nested stream is finished
   or when the iteratee is done. On the other hand, an Enumeratee
   is the Iteratee for the outer stream, taking data from the parent
   enumerator.
   One can view an Enumeratee as a AC/DC or voltage converter, or as
   a `vertical' composition of iteratees (compared to monadic bind, which
   plumbs two iteratees `horizontally')

   In the trivial case (e.g., Word8 to Char conversion), one element
   of the output stream is mapped to one element of the nested stream.
   Generally, we may need to read several elements from the outer stream to
   produce one element for the nested stream. Sometimes we can produce
   several nested stream elements from a single outer stream element.
  
   That many-to-many correspondence between the outer and the nested streams
   brings a complication. Suppose an enumeratee received an outer
   stream chunk of two elements elo1 and elo2. The enumeratee picked 
   elo1 and decoded it into a chunk of three elements eli1, eli2, and
   eli3, passing the chunk to the nested iteratee. The latter has read 
   eli1 and declared itself Done. The enumeratee has to return a value
   that contains the result of the nested Iteratee, and the 
   fact the element elo2 of the outer stream is left unprocessed.
   (We stress that we do _not_ report that there  are two elements left on
   the nested stream (eli2 and eli3): the nested stream is an internal
   resource of an enumeratee, which we do not leak out.)  We can
   report all these pieces of data if we pack them in a value
   of the following type
*)

type enumeratee 'elo 'eli 'a = 
  iteratee 'eli 'a -> iteratee 'elo (iteratee 'eli 'a)
;

(* We come to the same type in a different way. Suppose that the
   enumeratee has received EOF on its stream (that is, the outer stream).
   The enumeratee, as the outer iteratee, must move to the Done state. 
   Yet the nested iteratee is not finished. The enumeratee then has to
   return the nested iteratee as its result.
   The type of Enumeratee makes it clear that all effects of the inner
   Iteratee are absorbed into the outer Iteratee.
*)


(* One of the simplest Enumeratee: the nested stream is the prefix
   of the outer stream of exactly n elements long. Such nesting arises
   when several independent streams are concatenated.

   Read n elements from a stream and apply the given (nested) iteratee to the
   stream of the read elements. Unless the stream is terminated early, we
   read exactly n elements (even if the iteratee has accepted fewer).
   The last phrase implies that
          take n iter1 >> take m iter2
       is different from
          take (n+m) (iter1 >> iter2)
    in the case iter1 receives a chunk, moves to a done state after
    consuming a part of it. Then in (iter1 >> iter2), iter2 would get
    the rest of the chunk. In
          take n iter1 >> take m iter2
    iter2 would not get the rest of iter1's chunk. In fact, 
          take n iter1 >> take m iter2 
    is the same as
          drop n >> take m iter2 
   This behavior is intended: `take' reinforces fixed-length frame boundaries.
*)

value (take : int -> enumeratee 'el 'el 'a) n i =
  let rec take n i =
    if n = 0
    then return i
    else
      match i with
      [ IE_cont None k -> ie_cont (step n k)
      | IE_cont (Some _) _ | IE_done _ -> drop n >>= fun () -> return i
      ]
  and step n k s =
    match s with
    [ Chunk c ->
        let len = S.length c in
        if len = 0
        then ie_contM (step n k)
        else
          if len < n
          then
            k s >>% fun (i, _) ->
            IO.return (take (n - len) i, empty_stream)
          else
            let (s1, s2) = S.split_at n c in
            k (Chunk s1) >>% fun (i, _) ->
            ie_doneM i (Chunk s2)
    | EOF _ -> k s >>% fun (i, _) -> ie_doneM i s
    ]
  in
    take n i
;


(* Map the stream: yet another Enumeratee
   Given the stream of elements of the type elo and the function elo->eli,
   build a nested stream of elements of the type eli and apply the
   given iteratee to it.
   Note the contravariance.
   The difficult question is about left-over elements.
   Suppose the enumeratee received a chunk of elo elements,
   mapped them to eli elements and passed the chunk to the inner iteratee.
   The inner iteratee moved to a done state and reported N eli elements
   as not consumed.
   There are two choices for the result of the Enumeratee:
    no left-over elo elements; the inner iteratee in the Done state
    with N left-over eli elements
    N left-over elo elements; the inner iteratee in the Done state
    with 0 left-over eli elements.
   The second choice assumes that we can map from left-over eli elements
   back to the left-over elo elements. Since we map one elo
   element to one eli element, we can always determine how many
   elo elements left over from the number of remaining eli elements.
   For now, we go for the first choice, which seems simpler and
   more general.
*)

value (map_stream : ('elo -> 'eli) -> enumeratee 'elo 'eli 'a) f i =
  let rec map_stream i =
    match i with
    [ IE_cont None k -> ie_cont (step k)
    | IE_cont (Some _) _ | IE_done _ -> return i
    ]
  and step k s =
    match s with
    [ Chunk c ->
        if S.is_empty c
        then ie_contM (step k)
        else
          k (Chunk (S.map f c)) >>% fun (iv, _) ->
          IO.return (map_stream iv, empty_stream)
    | EOF _ ->
        ie_doneM (ie_cont k) s
    ]
  in
    map_stream i
;


(* Convert one stream into another, not necessarily in `lockstep'
   The transformer map_stream maps one element of the outer stream
   to one element of the nested stream. The transformer below is more
   general: it may take several elements of the outer stream to produce
   one element of the inner stream.
   The transformation from one stream to the other is specified as
   Iteratee elo m eli.
   This is a generalization for Monad.sequence
*)

value (sequence_stream : iteratee 'elo 'eli -> enumeratee 'elo 'eli 'a) fi i =
  let rec sequence_stream i =
    match i with
    [ IE_cont None k ->
        is_stream_finished >>= fun is_fin ->
        match is_fin with
        [ None -> step k
        | Some _ -> return i
        ]
    | IE_cont (Some _) _ | IE_done _ -> return i
    ]
  and step k =
    fi >>= fun v ->
    liftI ((k & chunk_of v) >>% fun (i, _s) ->
           IO.return (sequence_stream i))
  in
    sequence_stream i
;


value is_space c = (c = '\x20' || c = '\x09' || c = '\x0D' || c = '\x0A')
;


(* Convert the stream of characters to the stream of words, and
   apply the given iteratee to enumerate the latter.
   Words are delimited by white space.
   This is the analogue of hs' List.words
   More generally, we could have used sequence_stream to implement enum_words.
*)

value rec (enum_words : enumeratee char string 'a) i =
  match i with
  [ IE_cont None k ->
      drop_while is_space >>= fun () ->
      break_chars is_space >>= fun w ->
let () = dbg "enum_words: %S\n" w in
      if w = ""
      then return i  (* finished *)
      else
        liftI (
          k (chunk_of w) >>% fun (i, _s) ->
          (IO.return (enum_words i))
        )
  | IE_cont (Some _) _ | IE_done _ -> return i
  ]
;


end
;  (* `Make' functor *)

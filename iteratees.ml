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

open It_Ops
;

open Dbg
;

open It_Types
;

module Make (IO : MonadIO)
=
struct

module It_IO = IO;

module Subarray = Subarray
;

module S = Subarray
;

(* +
   In OCaml, Iteratees' [err_msg] is represented by simple exception.
   [err_msg] can be Iteratees' internal exception, user-defined Iteratees'
   exception, or an IO exception with place, wrapped into [Types.EIO]
   exception.

   IO exceptions (see MonadIO signature) carry the tuple of exception and
   the place where exception was raised (similar to
   [Unix.Unix_error (error, place, argument)] exception; I find it useful).

   Sometimes we need to wrap Iteratees' error into IO error:
   [Iteratees_err_msg err_msg] represents such wrapped exception.

   Functions [merr_of_ierr] (IO-monad error of Iteratees' error) and
   [ierr_of_merr] know about wrapping, and they unwrap such exceptions.
*)

type err_msg = exn;

exception EIO = It_Types.EIO;

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

value ierr_of_merr (e : exn) : err_msg =
  match e with
  [ Iteratees_err_msg e | e -> e
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
  | Chunk of Subarray.t 'el
  ]
;

value chunk_of elem = Chunk (S.of_elem elem)
;


value dbgstream ?addon s =
  match s with
  [ EOF eopt ->
      Printf.sprintf "s:EOF{e=%s}" &
      match eopt with
      [ None -> "None"
      | Some exn -> Printf.sprintf "Some{%s}" & Printexc.to_string exn
      ]
  | Chunk b -> Printf.sprintf "s:Chunk{arr[%i],ofs=%i,len=%i%s}"
      (Array.length b.S.arr) b.S.ofs b.S.len
      (match addon with
       [ None -> ""
       | Some a -> "," ^ a
       ]
      )
  ]
;


value dbgstream_char ?body s =
  match body with
  [ None -> dbgstream ?addon:None s
  | Some i ->
      match s with
      [ EOF _ -> ""
      | Chunk arr ->
          let (a1, _a2) = S.split_at i arr in
          Printf.sprintf "body=%S.." (S.to_string a1)
      ]
  ]
;

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


module Sl
 :
  sig
    type sl 'el;
    value empty : sl 'el;
    value destr_head : sl 'el -> option (stream 'el * sl 'el);
    value cons : stream 'el -> sl 'el -> sl 'el;
    value get_one_opt : sl 'el -> option (stream 'el);
    value one : stream 'el -> sl 'el;
    value append : sl 'el -> sl 'el -> sl 'el;
    value copy_my_buf : array 'el -> sl 'el -> sl 'el;

    value dbgsl : sl 'el -> string;
  end
 =
  struct
    type sl 'el = list (stream 'el);
    value empty = [];
    value destr_head = fun
      [ [] -> None
      | [h :: t] -> Some (h, t)
      ]
    ;
    value cons h t =
      match h with
      [ EOF _ ->
          let () = assert (t = []) in
          [h (* :: t=[] *)]
      | Chunk c ->
          if S.is_empty c
          then t
          else [h :: t]
      ]
    ;
    value get_one_opt = fun
      [ [] -> None
      | [h] -> Some h
      | _ -> assert False
      ];
    value one s = cons s [];

    value dbgsl sl =
      Printf.sprintf "sl:[%s]"
        (String.concat " ; " (List.map dbgstream sl))
    ;

    value rec append sl1 sl2 =
      match sl1 with
      [ [sl1h :: sl1t] -> cons sl1h (append sl1t sl2)
      | [] -> sl2
      ]
    ;

    value copy_my_buf buf_arr sl =
      List.map
        (fun s ->
           match s with
           [ EOF _ -> s
           | Chunk buf' ->
               if buf'.S.arr == buf_arr
               then Chunk (S.copy buf')
               else s
           ]
        )
        sl
    ;

  end
;

type sl 'el = Sl.sl 'el
;


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

(* +
   Some applications (look-ahead) require more complex type to store the
   rest of stream, especially when Chunk and EOF are already passed to
   iteratee and they should be processed without loosing part of stream or
   breaking iteratee's laws.
   So it will be the list of streams.
*)

type iteratee 'el 'a =
  [ IE_done of 'a
  | IE_cont of option err_msg
            and (stream 'el -> IO.m (iteratee 'el 'a  *  sl 'el))
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
  | IE_cont e k_a ->
      IE_cont e
        (fun s ->
           k_a s >>% fun
           [ (IE_done a, sl) ->
               match f a with
               [ (IE_cont None k_b) as it_b ->
                   loop_stream it_b k_b sl
                   where rec loop_stream it_b k_b sl =
                     match Sl.destr_head sl with
                     [ None -> IO.return (it_b, Sl.empty)
                     | Some (sl_h, sl_t) ->
                         k_b sl_h >>% fun (it_b, sl_h) ->
                         match it_b with
                         [ IE_done _ | IE_cont (Some _) _ ->
                             let sl = match Sl.get_one_opt sl_h with
                             [ None -> sl_t
                             | Some sl_h_h -> Sl.cons sl_h_h sl_t
                             ] in
                             IO.return (it_b, sl)
                         | IE_cont None k_b ->
                             loop_stream it_b k_b sl_t
                         ]
                     ]
               | (IE_cont (Some _) _ | IE_done _) as i ->
                   IO.return (i, sl)
               ]
           | (((IE_cont _) as i), sl) -> IO.return (bindI f i, sl)
           ]
        )
  ]
;

value ( =<< ) = bindI
;

value ( >>= ) m f = bindI f m
;


value (lift : IO.m 'a -> iteratee 'el 'a) m =
  IE_cont None (fun s -> m >>% fun x -> IO.return (return x, Sl.one s))
;


(* Throw an irrecoverable error *)

value rec throw_err e : iteratee 'el 'a =
  IE_cont (Some e) (throw_err_cont e)
and throw_err_cont e =
  fun s -> IO.return (throw_err e, Sl.one s)
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

value empty_stream = Chunk Subarray.empty
;


(* +
   [ie_doneM] and [ie_contM] are useful inside [IE_cont] continuation,
   they return from [IE_cont] either "iteratee returns [x] and maybe
   some data left in stream [s]", or "we have processed stream (1),
   but we have no result yet -- pass more data to the function [k]".
   "empty_stream" in ie_contM code is the reflection of fact (1).
*)

value
  ( ie_doneM : 'a -> stream 'el -> IO.m (iteratee 'el 'a  *  sl 'el) )
  x s = IO.return (IE_done x, Sl.one s)
;

value ie_contM k = IO.return (IE_cont None k, Sl.empty)
;


value ie_doneMsl x sl = IO.return (IE_done x, sl)
;


value rec ie_errorMsl e sl =
  IO.return (IE_cont (Some e) (fun s -> ie_errorMsl e (Sl.one s)), sl)
;


(* +
   Almost unusable in OCaml, since value monomorphism/restriction(?)
   for function applications (for [ie_cont some_cont]) bound to
   top-level values.  For top-level values, [IE_cont None some_cont]
   should be used instead.
*)

value (ie_cont : (stream 'el -> IO.m (iteratee 'el 'a * sl 'el)) ->
                 iteratee 'el 'a)
cont =
  IE_cont None cont
;


value (liftI : IO.m (iteratee 'el 'a) -> iteratee 'el 'a) m =
  ie_cont (fun s -> m >>% run' s)
  where run' s i =
    match i with
    [ IE_cont None k -> k s
    | IE_cont (Some _) _ | IE_done _ -> IO.return (i, Sl.one s)
    ]
;


value merr_of_ierr (e : err_msg) : IO.m 'a =
  IO.error &
  match e with
  [ EIO _ -> e
  | e -> Iteratees_err_msg e
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
      (inner_k (EOF None)) >>% fun (inner_iter2, _el'_sl) ->
      match inner_iter2 with
      [ IE_done inner_result -> ie_doneM inner_result outer_stream
      | IE_cont opt_err _inner_k2 ->
          match opt_err with
          [ Some e -> merr_of_ierr e
          | None -> IO.error (Divergent_iteratee "joinI")
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
          [ None -> (Divergent_iteratee "run")
          | Some e -> e
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


value get_stream_eof : iteratee 'el (option (option err_msg)) =
  IE_cont None (fun s ->
    ie_doneM
      (match s with
       [ EOF opt_err -> Some opt_err
       | Chunk _ -> None
       ]
      )
      s
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
     let r = Buffer.contents b in
     (* let () = dbg "break_chars: b=%i, cont=%S\n" (Obj.magic b) r in *)
     r
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
    | EOF _ -> IO.return (IE_cont (Some (set_eof s)) step, Sl.one s)
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

value rec drop_step n s =
  match s with
  [ Chunk c ->
      let len = c.S.len in
      if len < n
      then ie_contM (drop_step (n - len))
      else ie_doneM () (Chunk (S.drop n c))
  | EOF _ -> ie_doneM () s
  ]
;

value (drop : int -> iteratee 'el unit) n =
  if n = 0
  then return ()
  else IE_cont None (drop_step n)
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


(* +
   [enum_string ?chunk_size str] enumerates the string [str], using
   the [chunk_size] elements array.
*)

value enum_string
  ?(chunk_size=4096)
  str
 :
  enumerator char 'a
 =
  let str_len = String.length str in
  let arr_sz = min str_len chunk_size in
  let arr = Array.make arr_sz '\x00' in
  let fill_array ofs : int =
    let ilen = min arr_sz (str_len - ofs) in
    let imax = ilen - 1 in
    ( for i = 0 to imax do
        ( arr.(i) := str.[ofs + i]  (* todo: unsafe *)
        )
      done
    ; ilen
    )
  in
  inner 0
  where rec inner ofs it =
    match it with
    [ IE_done _ | IE_cont (Some _) _ -> IO.return it
    | IE_cont None k ->
        let len = fill_array ofs in
        if len = 0
        then
          IO.return it
        else
          k (Chunk (S.of_array_sub arr 0 len)) >>% fun (it, _s) ->
          inner (ofs + len) it
    ]
;

(*
value test_enum_string : unit =
 ignore (IO.runIO (
  (enum_string ~chunk_size:3 "abcdefg" (break_chars (fun _ -> False)))
  >>% fun it ->
  (I.run it)
  >>% fun res -> (failwith "res=%s" res ; IO.return ())
 ))
;
*)



value mprintf fmt = Printf.ksprintf (IO.write IO.stdout) fmt
;


value (mres : IO.m 'a -> IO.m (res 'a)) m =
  IO.catch
    (fun () -> m >>% fun r -> IO.return & `Ok r)
    (fun e -> IO.return & `Error e)
;

value (_munres : res 'a -> IO.m 'a) r =
  match r with
  [ `Ok x -> IO.return x
  | `Error ep -> IO.error ep
  ]
;


(* +
   Partial enumerators.
   In my concrete case they are needed when I've read some data and
   have to do some action without waiting for Chunk|EOF from stream
   (otherwise they are not needed; 'lift' would be enough (note that
   'lift' makes iteratee 'IE_cont None _')).

   In return type:
     option enumpart.. is None when sl contains EOF or EOF is got
     from enumerated resource; expecting that enumerator is deinited
     when returns None.

     When [Lazy.t (sl 'el)] is going to be used, it must be forced
     before next call to opt_enumpart.
 *)

type enumpart 'el 'a = sl 'el -> iteratee 'el 'a ->
  IO.m (iteratee 'el 'a * Lazy.t (sl 'el) * opt_enumpart 'el 'a)
and opt_enumpart 'el 'a =
  (* to avoid -rectypes *)
  [ EP_None
  | EP_Some of enumpart 'el 'a
  ]
;


value fdbg fmt = Printf.ksprintf (Printf.eprintf "forms: %s\n%!") fmt
;


value enumpart_readchars
 : ! 'ch .
   ~buffer_size:int ->
   ~read_func:('ch -> string -> int (*ofs*) -> int (*len*) -> IO.m int) ->
   'ch ->
   enumpart char 'a
 = fun ~buffer_size ~read_func inch sl it ->
     let buf_str = String.create buffer_size
     and buf_arr = Array.make buffer_size '\x00' in

     let rec feed sl k =
       match Sl.destr_head sl with
       [ None -> loop k
       | Some (sl_h, sl_t) ->
           k sl_h >>% fun (it, sl') ->
           check (Sl.append sl' sl_t) it
       ]
     and loop k =
       let () = fdbg "ep: loop" in
       mres (read_func inch buf_str 0 buffer_size) >>% fun read_res ->
       match read_res with
       [ `Error e ->
           k (EOF (some & ierr_of_merr e)) >>% fun (it, sl') ->
           IO.return (it, lazy sl', EP_None)
       | `Ok have_read ->
           mprintf "Read buffer, size %i\n" have_read >>% fun () ->
           let () = assert (have_read >= 0) in
           if have_read = 0
           then
             IO.return (ie_cont k, lazy Sl.empty, EP_None)
           else
             let c = S.replace_with_substring buf_arr buf_str 0 have_read in
             k (Chunk c) >>% fun (it, sl') ->
             check sl' it
       ]

     and check sl it =
       match it with
       [ IE_cont None k ->
           let () = fdbg "ep: check: cont" in
           feed sl k
       | IE_cont (Some _) _ | IE_done _ ->
           let () = fdbg "ep: check: ready" in
           IO.return (it, lazy (Sl.copy_my_buf buf_arr sl), EP_Some check)
       ]
     in
       check sl it
;


value enum_readchars
 : ! 'ch .
   ~buffer_size:int ->
   ~read_func:('ch -> string -> int (*ofs*) -> int (*len*) -> IO.m int) ->
   'ch ->
   enumerator char 'a
 = fun ~buffer_size ~read_func ch it ->
  enumpart_readchars ~buffer_size ~read_func ch
    Sl.empty
    it
  >>% fun (it, _sl_rest_l, _opt_enumpart) ->
  IO.return it
;


(* The enumerator of M's channels
   We use the same buffer all throughout enumeration
*)

value (enum_fd : IO.input_channel -> enumerator char 'a) inch =
  enum_readchars
    ~buffer_size:enum_fd_buffer_size.val
    ~read_func:IO.read_into
    inch
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

(*+
  Extended to be able to fail early when inner iteratee fails
  (so, no "frame boundaries"), this behaviour is achieved by passing
  [`Fail] as first argument.  Pass [`Drop] for original [take].
*)

value (take_gen : [= `Drop | `Fail ] -> int -> enumeratee 'el 'el 'a)
onerr n i =
  let rec take n i =
    if n = 0
    then return i
    else
      match (i, onerr) with
      [ (IE_cont None k, _) -> ie_cont (step n k)
      | (IE_cont (Some _) _, `Drop) | (IE_done _, _) ->
          drop n >>= fun () -> return i
      | (IE_cont (Some _) _, `Fail) ->
          return i
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
            IO.return (take (n - len) i, Sl.empty)
          else
            let (c1, c2) = S.split_at n c in
            k (Chunk c1) >>% fun (i, _) ->
            ie_doneM i (Chunk c2)
    | EOF _ -> k s >>% fun (i, _) -> ie_doneM i s
    ]
  in
    take n i
;

(*+
  Original [take]
*)
value take n i = take_gen `Drop n i;

(*+
  [take_or_fail] returns inner iteratee's error as early as possible,
  doesn't respecting frame boundaries.  This is useful when inner
  iteratee's error is fatal for the whole task.
*)
value take_or_fail n i = take_gen `Fail n i;


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
          IO.return (map_stream iv, Sl.empty)
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


(* Convert the stream of characters to the stream of words, and
   apply the given iteratee to enumerate the latter.
   Words are delimited by white space.
   This is the analogue of hs' List.words
   More generally, we could have used sequence_stream to implement enum_words.
*)

value rec (enum_words : enumeratee char string 'a) i =
  let is_space c = (c = '\x20' || c = '\x09' || c = '\x0D' || c = '\x0A') in
  match i with
  [ IE_cont None k ->
      drop_while is_space >>= fun () ->
      break_chars is_space >>= fun w ->
      (* let () = dbg "enum_words: %S\n" w in *)
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



value break_feed : ('a -> bool) -> enumeratee 'a 'a 'b = fun pred it_ ->
  let rec break_feed it =
    match it with
    [ IE_done _ | IE_cont (Some _) _ -> return it
    | IE_cont None k -> ie_cont & step k
    ]
  and step k s =
    match s with
    [ EOF _ -> ie_doneM (ie_cont k) s
    | Chunk c ->
       if S.length c = 0
       then
        ie_contM & step k
       else
        let (to_feed, to_leave) = S.break pred c in
        if S.is_empty to_feed
        then
          ie_doneM (ie_cont k) s
        else
          k (Chunk to_feed) >>% fun (it, sl) ->
          match it with
          [ IE_done _ | IE_cont (Some _) _ ->
              ie_doneMsl it (Sl.append sl & Sl.one & Chunk to_leave)
          | IE_cont None _k ->
              (* here: s is empty *)
              if S.is_empty to_leave  (* break not found *)
              then
                IO.return (break_feed it, Sl.empty)
              else
                ie_doneM it (Chunk to_leave)
          ]
    ]
  in
    break_feed it_
;


(* +
   [junk] = [drop 1]
*)

value junk = IE_cont None (fun s -> drop_step 1 s)
;


value array_ensure_size ~default array_ref size =
  if size < 0 || size > Sys.max_array_length
  then invalid_arg "Iteratees.array_ensure_size: bad size"
  else
  let realloc () =
    let new_size =
      loop 1
      where rec loop n =
        if n < size
        then loop (n * 2)
        else min n Sys.max_array_length
    in
    let r = Array.make new_size default in
    ( array_ref.val := r
    ; r
    )
  in
  let array = array_ref.val in
  if Array.length array < size
  then realloc ()
  else array
;



module SC = Subarray_cat
;

type uchar = int;
type utf16item = int;


module UTF8
 :
  sig
    value utf8_of_char : enumeratee char uchar 'a;
    value utf8_of_utf16 : enumeratee utf16item uchar 'a;
    value char_of_utf8 : enumeratee uchar char 'a;
  end
 =
  struct

    exception Bad_utf8 of string
    ;

    exception Bad_utf16 of string
    ;

    exception Bad_unicode of string
    ;

    value ensure_size = array_ensure_size ~default:(-1)
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


    value utf8_of_char uit =
      let arr_ref = ref [| |] in
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


    value bad16 fmt = Printf.ksprintf (fun s -> throw_err (Bad_utf16 s)) fmt;

    (* todo: in a more chunk-way *)

    value utf8_of_utf16 : enumeratee utf16item uchar 'a =
    fun it_ ->
      let is_surr c = (c >= 0xD800 && c <= 0xDFFF) in
      let rec utf8_of_utf16 it =
        break_feed is_surr it >>= fun it ->
        get_stream_eof >>= fun opt_opt_err ->
        match opt_opt_err with
        [ Some None -> return it
        | Some (Some err) -> throw_err err
        | None ->
            match it with
            [ IE_done _ | IE_cont (Some _) _ ->
                return it
            | IE_cont None k ->
                peek >>= fun hi_surr_opt ->
                match hi_surr_opt with
                [ None -> return it
                | Some hi_surr ->
                    if hi_surr < 0xD800 || hi_surr > 0xDBFF
                    then
                      bad16 "high surrogate out of range: 0x%x04" hi_surr
                    else
                      junk >>= fun () ->
                      peek >>= fun lo_surr_opt ->
                      match lo_surr_opt with
                      [ None -> throw_err
                          (Bad_utf16 "eof after high surrogate")
                      | Some lo_surr ->
                          junk >>= fun () ->
                          if lo_surr < 0xDC00 || lo_surr > 0xDFFF
                          then
                            throw_err (Bad_utf16 "low surrogate out of range")
                          else
                            let uchar = (hi_surr - 0xD800) * 0x400
                                        + lo_surr - 0xDC00 + 0x10000
                            in
                              let it =
                                liftI (k (chunk_of uchar) >>% fun (it, _sl) ->
                                       IO.return it)
                              in
                                utf8_of_utf16 it
                      ]
                  ]
            ]



        ]
      in
        utf8_of_utf16 it_
    ;


    exception Internal_bad_unicode of (int * int * int);

    value encode_utf8_error in_ofs_for_exn ofs c =
      raise (Internal_bad_unicode in_ofs_for_exn ofs c)
    ;

    value encode_utf8 in_ofs_for_exn c arr ofs =
      if (c < 0 || c >= 0x110000)
      then
        encode_utf8_error in_ofs_for_exn ofs c
      else if (c < 0x80)
      then
        ( arr.(ofs) := Char.chr c
        ; ofs + 1
        )
      else if (c < 0x0800)
      then
        ( arr.(ofs)     := Char.chr ((c lsr 6) land 0x1F lor 0xC0)
        ; arr.(ofs + 1) := Char.chr ( c        land 0x3F lor 0x80)
        ; ofs + 2
        )
      else if (c < 0x010000)
      then
        ( arr.(ofs)     := Char.chr ((c lsr 12) land 0x0F lor 0xE0)
        ; arr.(ofs + 1) := Char.chr ((c lsr  6) land 0x3F lor 0x80)
        ; arr.(ofs + 2) := Char.chr ( c         land 0x3F lor 0x80)
        ; ofs + 3
        )
      else (* if (c < 0x110000) then *)
        ( arr.(ofs)     := Char.chr ((c lsr 18) land 0x07 lor 0xF0)
        ; arr.(ofs + 1) := Char.chr ((c lsr 12) land 0x3F lor 0x80)
        ; arr.(ofs + 2) := Char.chr ((c lsr  6) land 0x3F lor 0x80)
        ; arr.(ofs + 3) := Char.chr ( c         land 0x3F lor 0x80)
        ; ofs + 4
        )
    ;

    value char_of_utf8 : enumeratee uchar char 'a = fun it_ ->
      let ensure_size = array_ensure_size ~default:'\x00' in
      let arrref = ref [| |] in
      let rec char_of_utf8 it =
        match it with
        [ IE_done _ | IE_cont (Some _) _ -> return it
        | IE_cont None k -> ie_cont & step k
        ]
      and step k s =
        match s with
        [ EOF _ -> ie_doneM (ie_cont k) s
        | Chunk c ->
            let in_len = S.length c in
            let arr = ensure_size arrref (in_len * 4) in
            let rec loop i o =
              if i = in_len
              then o
              else
                let new_ofs = encode_utf8 i (S.get c i) arr o in
                loop (i + 1) new_ofs
            in
            let loop_res =
              try `Ok (loop 0 0)
              with [ Internal_bad_unicode inofs outofs ch ->
                       `Error (inofs, outofs, ch) ] in
            let feed outofs =
              k (Chunk (S.of_array_sub arr 0 outofs)) >>% fun (it, _sl) ->
              IO.return it
            in
            match loop_res with
            [ `Error (inofs, outofs, ch) ->
                feed outofs >>% fun _it ->
                ie_errorMsl
                  (Bad_unicode (Printf.sprintf "character code 0x%X" ch))
                  (Sl.one (Chunk (S.drop inofs c)))
            | `Ok generated ->
                feed generated >>% fun it ->
                IO.return (char_of_utf8 it, Sl.empty)
            ]
        ]
      in
        char_of_utf8 it_
    ;

  end;  (* `UTF8' functor *)



(* [break_copy ~cpred ~outch] reads input just like [break ~cpred],
   but writes the input it has read into output channel [outch].
*)

value break_copy ~cpred ~outch : iteratee char unit =
  IE_cont None step
  where rec step s =
    match s with
    [ EOF _ as e -> ie_doneM () e
    | Chunk c ->
        if S.is_empty c
        then ie_contM step
        else
          let (matches, tail) = S.break cpred c in
          let matches_str = S.to_string matches in
          ( IO.write outch matches_str >>% fun () ->
            if S.is_empty tail
            then ie_contM step
            else ie_doneM () (Chunk tail)
          )
    ]
;


(* [break_limit ~pred ~limit] reads at most [limit] elements that
   don't satisfy predicate [pred], and returns when it either
   found element that satisfy [pred], or when [limit] elements were
   read and no satisfying element was found, or when there were an
   EOF or error found and neither any satisfying element was found
   nor [limit] elements was read.
   Returns: tuple [(status, subarray)], where
     [status = [= `Found | `Hit_limit | `Hit_eof ]]
     and [subarray] contains all the elements read.
   If the stream has exactly [limit] elements and no elements
   found, [`Hit_limit] is returned (limit has more priority
   than stream's end).
*)

value break_limit ~pred ~limit
: iteratee 'a ([= `Found | `Hit_limit | `Hit_eof] * Subarray.t 'a) =
  IE_cont None (step ~sc:(SC.make [S.empty]) ~left:limit)
  where rec step ~sc ~left s =
    let ret status sc s =
      ie_doneM (status, SC.sub_copy_out sc) s
    in
    if left = 0
    then
      ret `Hit_limit sc s
    else
      match s with
      [ EOF _ -> ret `Hit_eof sc s
      | Chunk c ->
          match S.break_limit ~limit:left pred c with
          [ `Found (prefix, rest) ->
              ret `Found (SC.append sc prefix) (Chunk rest)
              (* not copying here, since [ret->sub_copy_out] will copy *)
          | `Hit_limit ->
              let (prefix, rest) = S.split_at left c in
              step ~sc:(SC.append sc prefix) ~left:0 (Chunk rest)
              (* not copying here, since [step->ret->sub_copy_out] will copy *)
          | `Hit_end ->
              ie_contM &
                step
                  ~sc:(SC.append sc (S.copy c))
                  ~left:(left - S.length c)
          ]
      ]
;


value (limit : int -> enumeratee 'el 'el 'a) lim = fun it ->
  let rec limit ~lim ~it =
    let () = dbg "limit: lim=%i\n%!" lim in
    match (lim, it) with
    [ (_, (IE_done _ | IE_cont (Some _) _))
      | (0, IE_cont None _) -> return it
    | (lim, IE_cont None k) ->
        ie_cont & step ~left:lim ~k
    ]
  and step ~left ~k s
   : IO.m (iteratee 'el (iteratee 'el 'a) * sl 'el) =
    match (s : stream 'el) with
    [ EOF _ -> k s >>% fun (i, _) -> ie_doneM i s
    | Chunk c ->
        let len = S.length c in
        let () = dbg "limit/step: len=%i\n%!" len in
        if len <= left
        then
          k s >>% fun (it, s) ->
          IO.return (limit ~lim:(left - len) ~it, s)
        else
          let (c1, c2) = S.split_at left c in
          k (Chunk c1) >>% fun (it, s1') ->
            let s' = 
              match Sl.get_one_opt s1' with
              [ Some (Chunk c1') -> (Chunk (S.concat_splitted c1' c2))
              | None | Some (EOF _) -> (Chunk c2)
              ] in
            (*
            let () = dbg "limit: concated: %s\n%!" & dbgstream s' in
            *)
            ie_doneM it s'
    ]
  in
    limit ~lim ~it
;


value
  (catchk : (unit -> iteratee 'el 'a) ->
            ( err_msg ->
              (stream 'el -> IO.m (iteratee 'el 'a  *  sl 'el)) ->
              iteratee 'el 'a
            ) ->
            iteratee 'el 'a
  ) itf handler =
  let rec catchk it =
    match it with
    [ IE_done _ -> it
    | IE_cont (Some e) k ->
        try
          handler e k
        with
        [ e -> throw_err e ]
    | IE_cont None k -> ie_cont (step k)
    ]
  and step k s =
    (IO.catch
       (fun () -> k s >>% fun r -> IO.return (`Ok r))
       (fun e -> IO.return (`Error e))
    ) >>% fun
    [ `Ok (it, s') -> IO.return (catchk it, s')
    | `Error e -> IO.return (catchk (throw_err e), Sl.one s)
    ]
  in
    let () = dbg "catchk: entered\n%!" in
    let it =
      try
        itf ()
      with
      [ e -> throw_err e ]
    in
      catchk it
;


value
  (catch : (unit -> iteratee 'el 'a) ->
           ( err_msg ->
             iteratee 'el 'a
           ) ->
           iteratee 'el 'a
  ) itf handler =
  catchk itf (fun err_msg _cont -> handler err_msg)
;




value printf fmt =
  Printf.ksprintf (fun s -> lift & IO.write IO.stdout s) fmt
;


value gather_to_string : iteratee char string =
  prepend
    (fun () -> Buffer.create 50)
    (fun buf ->
       let rec step s =
         match s with
         [ Chunk c ->
             ( Subarray.buffer_add buf c
             ; ie_contM step
             )
         | EOF None ->
             ie_doneM (Buffer.contents buf) s
         | EOF (Some e) ->
             IO.error e
         ]
       in
       ie_cont step
    )
;

  module Ops
   :
    sig
      (* IO binds: *)
      value ( %<< ) : ('a -> It_IO.m 'b) -> It_IO.m 'a -> It_IO.m 'b;
      value ( >>% ) : It_IO.m 'a -> ('a -> It_IO.m 'b) -> It_IO.m 'b;

      (* Iteratees binds: *)
      value ( =<< ) :
        ('a -> iteratee 'el 'b) -> iteratee 'el 'a -> iteratee 'el 'b;
      value ( >>= ) :
        iteratee 'el 'a -> ('a -> iteratee 'el 'b) -> iteratee 'el 'b;

      (* Enumerators sequence: *)
      value ( >>> ) :
        enumerator 'el 'a -> enumerator 'el 'a -> enumerator 'el 'a
      ;

    end
   =
    struct
      value ( %<< ) = ( %<< );
      value ( >>% ) = ( >>% );

      value ( =<< ) = ( =<< );
      value ( >>= ) = ( >>= );

      (* Enumerators sequence: *)
      value ( >>> ) = ( >>> );
    end
  ;


(* Feed Iteratee a piece of stream. Disregard the remaining stream
   (the operation typically used by enumerators)
*)

value feedI
  (k : stream 'el -> IO.m (iteratee 'el 'a  *  sl 'el))
  (str : stream 'el)
 :
  IO.m (iteratee 'el 'a)
 =
  k str >>% (IO.return % fst)
;

(* +
   Feed iteratee if it wants to eat, otherwise leave it as is
   (ignoring the stream).  The rest of the stream is ignored anyway.
   Useful when iteratee is fed only when it is hungry.
*)
value feed_it :
  iteratee 'el 'a ->
  stream 'el ->
  iteratee 'el 'a
 =
  fun it s ->
    match it with
    [ IE_done _ | IE_cont (Some _) _ -> it
    | IE_cont None k ->
        liftI
          (k s >>% fun (it, _) -> IO.return it)
    ]
;


exception Itlist_empty;

module Anyresult_lasterror
 =
  struct

        value itlist_step_firstresult_lasterror
          (lst : list (iteratee 'el 'a))
          (s : stream 'el)
         :
          IO.m [= `First_result of (iteratee 'el 'a * sl 'el)
               |  `Last_error of err_msg
               |  `Cont of list (iteratee 'el 'a)
               ]
         =
          let rec loop lasterropt acc lst =
            match lst with
            [ [] ->
                if acc = []
                then
                  match lasterropt with
                  [ None -> assert False
                  | Some err -> IO.return & `Last_error err
                  ]
                else
                  IO.return & `Cont (List.rev acc)
            | [hd :: tl] ->
                match hd with
                [ (IE_done _) as it -> IO.return & `First_result (it, Sl.one s)
                | IE_cont ((Some _) as someerr) _ ->
                    loop someerr acc tl
                | IE_cont None k ->
                    k s >>% fun
                    [ (IE_done _, _) as r ->
                        IO.return & `First_result r
                    | (IE_cont (Some _ as someerr) _, _) ->
                        loop someerr acc tl
                    | ((IE_cont None _ as hd'), _s) ->
                        loop lasterropt [hd' :: acc] tl
                    ]
                ]
            ]
          in
            if lst = []
            then IO.return & `Last_error Itlist_empty
            else loop None [] lst
        ;

        value get_any_done lst =
          loop lst
          where rec loop lst =
            match lst with
            [ [ ((IE_done _) as x) :: _ ] -> Some x
            | [] -> None
            | [ (IE_cont _ _) :: _ ] -> loop lst
            ]
        ;

        value itlist_anyresult_lasterror
          (lst : list (iteratee 'el 'a))
         :
          iteratee 'el 'a
         =
          match get_any_done lst with
          [ Some x -> x
          | None -> ie_cont & step lst
              where rec step lst s =
                itlist_step_firstresult_lasterror lst s >>% fun
                [ `First_result r -> IO.return r
                | `Last_error e -> IO.error e
                | `Cont [] -> assert False
                | `Cont [it :: []] ->  IO.return (it, Sl.empty)
                | `Cont lst -> ie_contM & step lst
                ]
          ]
        ;

  end
;

(* +
   [itlist_anyresult_lasterror it_lst] takes a list of iteratees,
   passes input to all of them, and returns either the iteratee
   that left alone (when others are failed with error), or
   the last met error (when all iteratees have failed).
   When the empty list is given, error [Itlist_empty] is returned.
*)

value itlist_anyresult_lasterror
 :
  list (iteratee 'el 'a) -> iteratee 'el 'a
 =
  Anyresult_lasterror.itlist_anyresult_lasterror
;


exception SInt_overflow;
exception SInt_not_a_number of string;

module Reading_ints
 :
  sig
    value read_uint : iteratee char int;
    value read_uint_nz : iteratee char int;
    value read_int : iteratee char int;
    value read_int_nz : iteratee char int;

    value read_uint32 : iteratee char int32;
    value read_uint32_nz : iteratee char int32;
    value read_int32 : iteratee char int32;
    value read_int32_nz : iteratee char int32;

    value read_uint64 : iteratee char int64;
    value read_uint64_nz : iteratee char int64;
    value read_int64 : iteratee char int64;
    value read_int64_nz : iteratee char int64;
  end
 =
  struct

(*
    value ( & ) f x = f x;
*)

    module type SIGNED_INT
     =
      sig
        type t;
        value max_int : t;
        (* min_int = -max_int - 1 *)

        (* must work for small ints and small numbers:t : *)
        value of_int : int -> t;
        value to_int : t -> int;

        (* may overflow silently: *)
        value ( + ) : t -> t -> t;
        value ( - ) : t -> t -> t;
        value ( * ) : t -> t -> t;

        (* should truncate towards zero: *)
        value ( / ) : t -> t -> t;

        value ( <? ) : t -> t -> bool;
        value ( =? ) : t -> t -> bool;
      end
    ;

    module SInt_T : SIGNED_INT with type t = int
     =
      struct
        type t = int;
        value max_int = Pervasives.max_int;
        value of_int x = x;
        value to_int x = x;
        value ( + ) = Pervasives.( + );
        value ( - ) = Pervasives.( - );
        value ( * ) = Pervasives.( * );
        value ( / ) = Pervasives.( / );
        value ( <? ) = Pervasives.( < );
        value ( =? ) = Pervasives.( == );
      end
    ;

    module SInt32_T : SIGNED_INT with type t = int32
     =
      struct
        type t = int32;
        value max_int = Int32.max_int;
        value of_int = Int32.of_int;
        value to_int = Int32.to_int;
        value ( + ) = Int32.add;
        value ( - ) = Int32.sub;
        value ( * ) = Int32.mul;
        value ( / ) = Int32.div;
        value ( <? ) a b = (Int32.compare a b) < 0;
        value ( =? ) a b = (Int32.compare a b) = 0;
      end
    ;

    module SInt64_T : SIGNED_INT with type t = int64
     =
      struct
        type t = int64;
        value max_int = Int64.max_int;
        value of_int = Int64.of_int;
        value to_int = Int64.to_int;
        value ( + ) = Int64.add;
        value ( - ) = Int64.sub;
        value ( * ) = Int64.mul;
        value ( / ) = Int64.div;
        value ( <? ) a b = (Int64.compare a b) < 0;
        value ( =? ) a b = (Int64.compare a b) = 0;
      end
    ;

    module SInt_F (S : SIGNED_INT)
     :
      sig
        (* value digits : S.t -> int; *)

        value read_unsigned_gen : ~allow0:bool -> iteratee char S.t;
        value read_signed_gen : ~allow0:bool -> iteratee char S.t;
      end
     =
      struct
        open S;

        value zero = of_int 0
        ;

        value ( ~- ) n = zero - n
          and ( >? ) a b = not (a <? b) && not (a =? b)
          and ( >=? ) a b = not (a <? b)
          and ( <>? ) a b = not (a =? b)
        ;

        value one = of_int 1
        ;

        value minus_one = (- one)
        ;

        value min_int = (- max_int) - one
        ;

        value ten = of_int 10
        ;

        value rec digits_count n =
          Pervasives.( + )
            1
            (let n' = n / ten in
             if n' =? zero
             then 0
             else digits_count n'
            )
        ;

        value rem a b = (a - (a / b) * b)
        ;

        module P = Pervasives;

        value string_reverse_inplace str = P.(
          let len = String.length str in
          let len1 = len - 1 in
          let len2 = len / 2 - 1 in
          ( for i = 0 to len2
            do
              let j = P.( - ) len1 i in
              let tmp = str.[i] in
              ( str.[i] := str.[j]
              ; str.[j] := tmp
              )
            done
          ; str
          )
        );

        value min_int_digits = digits_count min_int;
        value max_int_digits = digits_count max_int;

        value to_base_abs b n =
          let buf = Buffer.create max_int_digits in
          let intb = to_int b in
          let digit n =
            let n = abs (to_int n) in
            ( assert (n < intb)
            ; assert (n < 10)
            ; Char.chr (P.( + ) n (Char.code '0'))
            ) in
          let rec loop n =
            let d = rem n b in
            let c = digit d in
            let () = Buffer.add_char buf c in
            let n' = n / b in
            if n' =? zero
            then string_reverse_inplace (Buffer.contents buf)
            else loop n'
          in
            loop n
        ;

        value to_dec_abs = to_base_abs ten
        ;

        value max_int_dec_abs = to_dec_abs max_int;

        value min_int_dec_abs = to_dec_abs min_int;


        value from_base_neg b ~maxstr str =
          let len = String.length str in
          let rec loop acc i =
            if i = len
            then acc
            else
              let digit ch =
                if (ch >= '0' && ch <= '9')
                then
                  let d = of_int (P.( - ) (Char.code ch) (Char.code '0')) in
                  if d >=? b
                  then raise (SInt_not_a_number "")
                  else d
                else assert False
              in
              let ch = str.[i] in
              let acc' = acc * b - digit ch in
              loop acc' (P.( + ) i 1)
          in
            if len = 0
            then `Empty
            else
            let maxlen = String.length maxstr in
            if len > maxlen
            then
              (* let () = dbgn "(from_base: len>maxlen) %!" in *)
              `Overflow
            else if len = maxlen && str > maxstr
            then
              (* let () = dbgn "(from_base: str>maxstr: %S > %S) %!"
                str maxstr
              in *)
              `Overflow
            else
              try
                `Ok (loop zero 0)
              with
              [ SInt_not_a_number _ -> `Not_a_number ]
        ;

        value from_dec_neg ~maxstr = from_base_neg ~maxstr ten
        ;

        value is_digit c = (c <= '9' && c >= '0')
        ;

        value is_not_digit c = not (is_digit c)
        ;

        value inan msg = throw_err (SInt_not_a_number msg)
        ;

        value peek_digit =
          peek >>= fun optc ->
          return (
            match optc with
            [ Some c when is_digit c -> optc
            | None | Some _ -> None
            ]
          )
        ;

        value read_gen
          ~allow0
          ~max_num_digits
          ~maxstr
          ~sign
         :
          iteratee char S.t
         =
          let rec read_beginning ~read0 =
            peek_digit >>= fun optd ->
            match optd with
            [ None ->
                if read0
                then return (Some zero)
                else inan "begins with not a digit"
            | Some d ->
                match (d, read0, allow0) with
                [ ('0', _, True)
                | ('0', False, False) ->
                  junk >>= fun () ->
                  read_beginning ~read0:True
                | (_, True, False) -> inan "leading zeroes"
                | (_, False, _) -> return None
                | (_, True, True) -> return None
                ]
            ]
          in
          read_beginning ~read0:False >>= fun
          [ Some r -> return r
          | None ->
               (limit max_num_digits &
                break_chars is_not_digit
               ) >>= fun it ->
               joinI (return it) >>= fun res ->
               peek_digit >>= fun optd ->
               match (it, res, optd) with
               [ (IE_done _, _, Some _) ->
                   assert False
                   (* limit should return IE_cont *)
               | (IE_cont (Some _) _, _, _) ->
                   assert False
                   (* joinI should raise this error *)
               | (IE_done str, _, None)
               | (IE_cont None _, str, None) ->
                   let () = assert
                     (String.length str <= max_num_digits) in
                   match from_dec_neg ~maxstr str with
                   [ `Not_a_number -> assert False
                   | `Empty -> assert False
                   | `Ok r -> return (r * (-sign))
                   | `Overflow -> throw_err SInt_overflow
                   ]

               | (IE_cont _ _, _, Some _) ->
                   (* let () = dbgn "(read_gen: cont/digit) %!" in *)
                   throw_err SInt_overflow
               ]
          ]
        ;

        value read_unsigned_gen ~allow0 =
          read_gen
            ~allow0
            ~max_num_digits:max_int_digits
            ~sign:one
            ~maxstr:max_int_dec_abs
        ;

        value read_negative_gen ~allow0 =
          read_gen
            ~allow0
            ~max_num_digits:min_int_digits
            ~sign:minus_one
            ~maxstr:min_int_dec_abs
        ;

        value read_signed_gen
          ~allow0
         :
          iteratee char S.t
         =
          peek >>= fun
          [ Some '-' -> junk >>= fun () -> read_negative_gen ~allow0
          | Some '+' -> junk >>= fun () -> read_unsigned_gen ~allow0
          | _ -> read_unsigned_gen ~allow0
          ]
        ;

      end
    ;

    module SInt = SInt_F(SInt_T)
    ;

    module SInt32 = SInt_F(SInt32_T)
    ;

    module SInt64 = SInt_F(SInt64_T)
    ;

    value read_uint_nz = SInt.read_unsigned_gen ~allow0:False;
    value read_uint = SInt.read_unsigned_gen ~allow0:True;
    value read_int_nz = SInt.read_signed_gen ~allow0:False;
    value read_int = SInt.read_signed_gen ~allow0:True;

    value read_uint32_nz = SInt32.read_unsigned_gen ~allow0:False;
    value read_uint32 = SInt32.read_unsigned_gen ~allow0:True;
    value read_int32_nz = SInt32.read_signed_gen ~allow0:False;
    value read_int32 = SInt32.read_signed_gen ~allow0:True;

    value read_uint64_nz = SInt64.read_unsigned_gen ~allow0:False;
    value read_uint64 = SInt64.read_unsigned_gen ~allow0:True;
    value read_int64_nz = SInt64.read_signed_gen ~allow0:False;
    value read_int64 = SInt64.read_signed_gen ~allow0:True;

  end
;

(* +
   Functions for reading decimal integers have names like
   [read_uint32_nz].  The pattern for functions' names is:

   read_[u]int{,32,64}[_nz]

   - Optional "u" means "read unsigned int", without '+' or '-' as
   the first char.
   - Type of the int to read is "int", "int32" or "int64".
   - "_nz" means "do not allow leading zeroes".  (note that "0" and "-0"
     does not have leading zeroes).

   The errors possible while reading ints are:
   - [SInt_overflow] when integer does not fit the range
   - [SInt_not_a_number (reason : string)] when the stream does not
     have the integer you need: for example, when there is EOF,
     not-a-digit char, any sign while you want to read unsigned integer,
     or leading zero while you want to read integer without leading zeroes.
*)
include Reading_ints
;


module type NUM
 =
  sig
    type num;
    value num_of_int : int -> num;
    value mult_num : num -> num -> num;

    (* [power_num a b] = "a^b", b \in Z *)
    value power_num : num -> num -> num;

    (* should work for "big integers" at least: *)
    value num_of_string : string -> num;
  end
;


(* +
   Create a module with functor [Reading_num(Num)] (the standard [Num]
   is just fine), and read numbers with decimal fixed point representation,
   like "1.23", "2.", ",123", "-00012.3".

   Exception [ENum "reason"] is raised when it's impossible to read
   a number from input.
*)

module Reading_num(Num : NUM)
 :
  sig
    (* +
       This function reads unsigned numbers without leading spaces.
    *)
    value num_fix_unsigned : iteratee char Num.num;

    (* +
       This function reads optionally signed numbers without leading spaces.
    *)
    value num_fix : iteratee char Num.num;

    (* +
       This is a convenience function for reading optionally signed numbers
       with optional spaces in front of them.  Errors are reported with the
       IO monad.
    *)
    value num_of_string_fix : string -> IO.m Num.num;
  end
 =
  struct

    value identity x = x
    ;

    exception ENum of string
    ;

    value num_err msg = throw_err (ENum msg)
    ;

    value is_decimal_point = fun [ '.' | ',' -> True | _ -> False ]
    ;

    value is_digit c = (c <= '9' && c >= '0')
      and is_not_digit c = (c < '0' || c > '9')
    ;

    value num_fix_unsigned =
      let ten = Num.num_of_int 10 in
      break_chars is_not_digit
      >>= fun before_point ->
      peek
      >>= fun optc ->
      match optc with
      [ Some c when is_decimal_point c ->
          junk >>= fun () ->
          return (String.make 1 c)
      | _ ->
          return ""
      ]
      >>= fun point ->
      break_chars is_not_digit >>= fun after_point ->
      if before_point = "" && after_point = ""
      then
        if point = ""
        then
          num_err "not a number (no digits, no decimal point)"
        else
          num_err & Printf.sprintf
            "decimal number can't consist of %S only"
            point
      else
        let scale = String.length after_point in
        return &
        let num = Num.num_of_string (before_point ^ after_point) in
        if scale = 0
        then num (* integers and rationals are represented differently,
                    and I don't know whether [Num.mult_num n (1/10)^0]
                    will keep [n] integer. *)
        else
          Num.mult_num
            num
            (Num.power_num ten (Num.num_of_int (-scale)))
    ;


    value num_fix =
      let num_negate = fun n -> Num.mult_num (Num.num_of_int (-1)) n in

      peek
      >>= fun optc ->
      match optc with
      [ None -> num_err "EOF while reading number"
      | Some '-' -> junk >>= fun () -> return num_negate
      | Some '+' -> junk >>= fun () -> return identity
      | _ -> return identity
      ]
      >>= fun make_sign ->
      num_fix_unsigned >>= fun num_unsigned ->
      return (make_sign num_unsigned)
    ;

    value is_whitespace = fun [ ' ' | '\t' -> True | _ -> False ]
    ;

    value num_of_string_fix str : IO.m Num.num =
      (run %<< enum_string str
        (drop_while is_whitespace >>= fun () ->
         num_fix >>= fun r ->
         peek >>= fun
         [ None -> return r
         | Some c -> num_err (Printf.sprintf
             "garbage after number: char %C" c)
         ]
        )
      )
    ;

  end
;



module Base64
 =
  struct

    (* the logic is stolen from OCaml library "cryptokit" version 1.5 *)

    value base64_conv_table =
      "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

    exception Bad_encoding;

    value base64_decode_char c =
      match c with
      [ 'A' .. 'Z' -> (Char.code c) - 65
      | 'a' .. 'z' -> ((Char.code c) - 97) + 26
      | '0' .. '9' -> ((Char.code c) - 48) + 52
      | '+' -> 62
      | '/' -> 63
      | ' ' | '\t' | '\n' | '\r' -> (-1)
      | '=' -> (-2)
      | _ -> (-3)
      ]
    ;

    value base64_decode_piece ~ibuf ~arr_to ~arr_ofs =
      ( arr_to.(arr_ofs) :=
          Char.chr ((ibuf.(0) lsl 2) + (ibuf.(1) lsr 4))
      ; arr_to.(arr_ofs + 1) :=
          Char.chr (((ibuf.(1) land 15) lsl 4) + (ibuf.(2) lsr 2))
      ; arr_to.(arr_ofs + 2) :=
          Char.chr (((ibuf.(2) land 3) lsl 6) + ibuf.(3))
      )
    ;

    value base64_decode ~s_from ~arr_to ~ibuf ~ipos =
      let s_len = S.length s_from in
      inner 0 0
      where rec inner s_ofs arr_ofs =
        if s_ofs = s_len
        then (arr_ofs, False, False)
        else
          match base64_decode_char (S.get s_from s_ofs) with
          [ (-1) -> inner (s_ofs + 1) arr_ofs
          | (-2) -> (arr_ofs, True, False)
          | (-3) -> (arr_ofs, False, True)
          | n ->
              ( ibuf.(ipos.val) := n
              ; incr ipos
              ; if ipos.val = 4
                then
                  ( base64_decode_piece ~ibuf ~arr_to ~arr_ofs
                  ; ipos.val := 0
                  ; Array.fill ibuf 0 4 0
                  ; inner (s_ofs + 1) (arr_ofs + 3) 
                  )
                else
                  inner (s_ofs + 1) arr_ofs
              )
          ]
    ;

    value base64_decode_last ~arr_to ~ibuf ~ipos_val (* : (written, error) *) =
      match ipos_val with
      [ 0 ->
          (0, False)
      | 1 ->
          (0, True)
      | 2 ->
          ( arr_to.(0) :=
              Char.chr ((ibuf.(0) lsl 2) + (ibuf.(1) lsr 4))
          ; (1, False)
          )
      | 3 ->
          ( arr_to.(0) :=
              Char.chr ((ibuf.(0) lsl 2) + (ibuf.(1) lsr 4))
          ; arr_to.(1) :=
              Char.chr (((ibuf.(1) land 15) lsl 4) + (ibuf.(2) lsr 2))
          ; (2, False)
          )
      | _ ->
          assert False
      ]
    ;


    (* from litpro; to merge *)
    value enee_cont
     = fun it step ->
      match it with
      [ IE_cont None k ->
          is_stream_finished >>= fun is_fin ->
          match is_fin with
          [ None -> step k
          | Some _ -> return it
          ]
      | IE_cont (Some _) _ | IE_done _ -> return it
      ]
    ;

    value enee_cont_io
     = fun it step ->
      match it with
      [ IE_cont None k ->
          step k
      | IE_cont (Some _) _ | IE_done _ -> ie_doneM it (Chunk S.empty)
      ]
    ;

    value rec enee_base64_decode
     : iteratee char 'a -> iteratee char (iteratee char 'a)
     = fun it ->
         enee_cont it & fun k -> ie_cont & step 
           (Array.make 4 0) (ref 0) (ref [| |]) k

    and step ibuf ipos obuf k =
      fun s ->
        match s with
        [ EOF opt_err -> finish ~opt_err ~ibuf ~ipos ~obuf k
        | Chunk s_from ->
            let max_out_size = ((S.length s_from) / 4 + 2) * 3 in
            let arr_to = array_ensure_size ~default:'\x00' obuf max_out_size in
            let (written, finished, error) =
              base64_decode ~s_from ~arr_to ~ibuf ~ipos in
            pass_obuf ~written ~arr_to k >>% fun it ->
            enee_cont_io it & fun k ->
            if error
            then
              ret k ~opt_err:(Some Bad_encoding)
            else
              if finished
              then
                finish ~obuf ~opt_err:None ~ibuf ~ipos k
              else
                ie_contM (step ibuf ipos obuf k)
        ]

    and finish ~obuf ~ibuf ~ipos ~opt_err k =
      let arr_to = array_ensure_size ~default:'\x00' obuf 3 in
      let (written, error) =
        base64_decode_last ~arr_to ~ibuf ~ipos_val:ipos.val in
      pass_obuf ~written ~arr_to k >>% fun it ->
      enee_cont_io it & fun k ->
      ret k ~opt_err:
        (match opt_err with
         [ Some _ -> opt_err
         | None -> if error then Some Bad_encoding else None
         ])

    and pass_obuf ~written ~arr_to k =
      if written > 0
      then
        let osub = S.of_array_sub arr_to 0 written in
          feedI k (Chunk osub)
      else
         IO.return (ie_cont k)

    and ret ~opt_err k =
      k (EOF opt_err) >>% fun (it, sl) -> ie_doneMsl it sl
    ;

  end
;


value base64_decode = Base64.enee_base64_decode
;


module Deque_stream
 :
  sig
    type t 'el;
    value empty : t 'el;
    value cons : int -> stream 'el -> t 'el -> t 'el;
    value cons_sl : sl 'el -> t 'el -> t 'el;
    value snoc : t 'el -> int -> stream 'el -> t 'el;
    value concat : t 'el -> sl 'el;
    value destr_head : t 'el -> option ((int * stream 'el) * t 'el);
    value is_empty : t 'el -> bool;
  end
 =
  struct

    (* очередь = deque of (ofs * chunk), где последний чанк не скопирован
       (т.е. добавление чанка в конец вызывает сначала копирование
       предыдущего чанка) -- можем рассчитывать только на нескопированность
       последнего чанка.
       копирование будет однократным, так как из хвоста чанки не берутся,
       а только добавляются туда.
    *)
    type t 'el = list (int * stream 'el);

    value empty = [];

    (*  добавить чанк в конец с копированием предыдущего чанка
        (копировать только кусок от ofs до len) *)
    value rec snoc init ofs stream =
      match init with
      [ [] -> [(ofs, stream)]
      | [(h_ofs, h_stream) :: []] ->
          match h_stream with
          [ Chunk c ->
              let h_stream = Chunk (S.copy
                (S.drop h_ofs c))
              in
                [(0, h_stream) :: [(ofs, stream)]]
          | EOF _ -> assert False
          ]
      | [h :: ([_ :: _] as t)] -> [h :: snoc t ofs stream]
      ]
    ;

    (* склеить очередь (копирование).  обязано скопировать последний чанк,
       не являющийся eof, так как его могут поменять. *)
    value rec concat q : sl _ =
      let to_add ~allow_eof ~copy ofs h_stream =
        match h_stream with
        [ EOF _ -> if allow_eof then h_stream else assert False
        | Chunk c ->
            if ofs = 0 && not copy
            then h_stream
            else
              let c = S.drop ofs c in
              let c = if copy then S.copy c else c in
              Chunk c
        ]
      in
      match q with
      [ [] -> Sl.empty
      | [(h_ofs, h_stream) :: []] ->
          Sl.one (to_add ~allow_eof:True ~copy:True h_ofs h_stream)
      | [(h_ofs, h_stream) :: ([_ :: _] as tl)] ->
          Sl.cons
            (to_add ~allow_eof:False ~copy:False h_ofs h_stream)
            (concat tl)
      ]
    ;

    value destr_head q =
      match q with
      [ [] -> None
      | [h :: t] -> Some (h, t)
      ]
    ;

    value cons ofs stream tail =
      match (stream, tail) with
      [ (EOF _, [_ :: _]) -> assert False
      | ((EOF _ | Chunk _), _) -> [(ofs, stream) :: tail]
      ]
    ;

    value rec cons_sl sl tail =
      match Sl.destr_head sl with
      [ None -> tail
      | Some (h_stream, t_sl) ->
          cons 0 h_stream (cons_sl t_sl tail)
      ]
    ;

    value is_empty t = (t = [])
    ;

  end
;


(*
на первом шаге it_subseq_step должен выдавать None для ". не нашли"
и Some (то, что дают итераты, только в option) для "! есть значение"
или "? хочу ещё данных"
*)

value break_subsequence
 : (S.t 'el -> int -> option (IO.m (iteratee 'el 'a * sl 'el))) ->
   iteratee 'el 'b ->
   iteratee 'el (option 'a * iteratee 'el 'b)
 = fun it_subseq_step it_proc ->

let rec break_subsequence q it_proc =
  (* иначе -- loop_q с очередью *)
  loop_q q it_proc

and break_subsequence_ret q ~sub_res_opt it_proc =
  ie_doneMsl (sub_res_opt, it_proc) (Deque_stream.concat q)

and feed_proc it_proc s =
  match it_proc with
  [ IE_done _ | IE_cont (Some _) _ -> IO.return it_proc
  | IE_cont None k_proc ->
      let () = fdbg "bs: feed_proc: %s" (dbgstream s) in
      k_proc s >>% fun (it_proc, _sl) ->
      IO.return it_proc
  ]

and loop_q q it_proc =
  match Deque_stream.destr_head q with
  [ None ->
      let () = fdbg "bs: loop_q: empty q" in
      ie_contM (step0 it_proc)
  | Some ((first_ofs, first_stream), qtail) ->
      let () = fdbg "bs: loop_q: first_stream = %s, first_ofs = %i"
        (dbgstream first_stream) first_ofs in
      match first_stream with
      [ EOF _ ->
          feed_proc it_proc first_stream >>% fun it_proc ->
          ie_doneMsl (None, it_proc) (Sl.one first_stream)
      | Chunk first_chunk ->
          loop_index first_chunk first_ofs it_proc ~qtail
      ]
  ]

and step0 it_proc =
  (* запрашиваем чанк, loop_index с первым чанком,
     смещением=0 и пустым хвостом.  вызывается из loop_q. *)
  fun s ->
    let () = fdbg "bs: step0: stream = %s" (dbgstream s) in
    match s with
    [ Chunk c -> loop_index c 0 it_proc ~qtail:Deque_stream.empty
    | (EOF _ ) as s -> ie_doneM (None, it_proc) s
    ]

and loop_index (first_chunk : S.t _) first_ofs it_proc ~qtail =

  (* Кормить = *)
  let feed_first_chunk ~cur_ofs it_proc =
    (* кормим it_proc куском текущего чанка от начального до текущего
       смещения, имеющихся в значениях loop_index *)
    let len = cur_ofs - first_ofs in
    let () = assert (len >= 0) in
    let () = fdbg "bs: feed_first_chunk: %i .. %i (len = %i)"
      first_ofs cur_ofs len in
    if len = 0
    then IO.return it_proc
    else
      let stream = Chunk (S.sub first_chunk ~ofs:first_ofs ~len) in
      feed_proc it_proc stream
  in

  (* пытаемся последовательно по всем смещениям применить it_subseq_step: *)
  let first_len = S.length first_chunk in
  let rec loop_ofs ofs =
    let () = assert (ofs <= first_len) in
    (* let () = fdbg "bs: loop_ofs: ofs = %i, first_ofs = %i" ofs first_ofs
    in *)
    (* проверка на конец должна быть в начале, так как step1 может
       дать ofs=len *)
    if ofs = first_len
    then
      (* - когда дошли до конца чанка, *)
      (*   - Кормить *)
      feed_first_chunk ~cur_ofs:ofs it_proc >>% fun it_proc ->
      (*   - идём дальше: break_subsequence по хвосту (там же оно выйдет,
             если итерат кончил), и остаток потока тут не важен *)
      break_subsequence qtail it_proc
    else
      match it_subseq_step first_chunk ofs with
      [ None ->
          (* - пока ошибка, идём по чанку к следующему смещению. *)
          (* let () = fdbg "bs: loop_ofs: None from subseq" in *)
          loop_ofs (ofs + 1)
      | Some io_sq_it_left ->
          let () = fdbg "bs: loop_ofs: Some _ from subseq" in
          io_sq_it_left >>% fun (sq_it, sq_left) ->
          let () = fdbg "bs: loop_ofs: sq_left = %s"
            (Sl.dbgsl sq_left)
          in
          match sq_it with
          [ IE_done sub_res ->
             (* - когда результат от it_subseq_step -- *)
             (*   - Кормить *)
             feed_first_chunk ~cur_ofs:ofs it_proc >>% fun it_proc ->
             (*   - возвращаем его и результат от it_subseq_step *)
             let q = Deque_stream.cons_sl sq_left qtail in
             break_subsequence_ret ~sub_res_opt:(Some sub_res) q it_proc
          | IE_cont (Some _) _ -> ie_errorMsl (Invalid_argument
              "break_sequence: it_subseq_step should return None on error")
              Sl.empty
          | IE_cont None k_sub ->
              (* - когда не ошибка, а "хочу ещё" от it_subseq_step -- *)
              (*   - Кормить *)
              feed_first_chunk ~cur_ofs:ofs it_proc >>% fun it_proc ->
              step1 k_sub it_proc qtail
          ]  (* match sq_it *)
      ]  (* match it_subseq_step option *)
  in
    loop_ofs first_ofs

(* запросить ещё чанки для тестирования их продолжением k_sub *)
and step1 k_sub it_proc q =
  (* запрашиваем чанк *)
  ie_contM & fun s ->
  let q = Deque_stream.snoc q 0 s in
  (* дать s в k_sub, посмотреть на результат *)
  k_sub s >>% fun (it_sub, sl_sub) ->
  match it_sub with
  [ IE_done r ->
      break_subsequence_ret
        (Deque_stream.cons_sl sl_sub Deque_stream.empty)
        ~sub_res_opt:(Some r)
        it_proc

  | IE_cont (Some _) _ ->
       (* - если ошибка -- loop_index со следующего смещения в первом чанке
            очереди (может дать ofs=len) *)
       match Deque_stream.destr_head q with
       [ None -> assert False
       | Some ((first_ofs, first_stream), qtail) ->
           match first_stream with
           [ EOF _ ->
               let () = assert (Deque_stream.is_empty qtail) in
               feed_proc it_proc first_stream >>% fun it_proc ->
               break_subsequence_ret
                 q
                 ~sub_res_opt:None
                 it_proc

           | Chunk first_chunk ->
               loop_index first_chunk (first_ofs + 1) it_proc ~qtail
           ]
       ]

  | IE_cont None k_sub -> step1 k_sub it_proc q
  ]
in
  ie_cont & fun s ->
    let () = fdbg "bs: init: stream = %s" (dbgstream s) in
    break_subsequence Deque_stream.(cons 0 s empty) it_proc
;


value rec it_ignore_or_fail : iteratee 'el unit =
  IE_cont None it_ignore_step
and it_ignore_step = fun
  [ EOF None as s -> ie_doneM () s
  | (EOF (Some e)) as s -> ie_errorMsl e (Sl.one s)
  | Chunk _ -> ie_contM it_ignore_step
  ]
;


value rec it_ignore : iteratee 'el unit =
  IE_cont None it_ignore_step
and it_ignore_step = fun
  [ (EOF _) as s -> ie_doneM () s
  | Chunk _ -> ie_contM it_ignore_step
  ]
;


value map_ready
 : ! 'el1 'el2 'a .
   iteratee 'el1 'a ->
   iteratee 'el2 'a
 = fun it ->
     joinI & return it
;


value eof_to_res
 : ! 'el1 'el2 'a .
   iteratee 'el1 'a ->
   option err_msg ->
   iteratee 'el2 [= `Ok of 'a | `Error of err_msg ]
 = fun it opt_err ->
     match it with
     [ IE_done a -> IE_done (`Ok a)
     | IE_cont (Some e) _k -> IE_done (`Error e)
     | IE_cont None k ->
         lift
           (IO.catch
              (fun () ->
                 k (EOF opt_err) >>% fun (it, _) ->
                 match it with
                 [ IE_done r -> IO.return (`Ok r)
                 | IE_cont (Some e) _ -> IO.return (`Error e)
                 | IE_cont None _ -> IO.error (Divergent_iteratee "eof_to_res")
                 ]
              )
              (fun e -> IO.return (`Error e))
           )
     ]
;


(* for break_subsequence *)

value probe_string str
 : S.t 'el -> int -> option (IO.m (iteratee char unit * sl char))
 = fun arr ofs ->
     let rec cmp arr ~ofs ~i =
       if i = String.length str
       then `Yes ofs
       else
         let len = S.length arr in
         if ofs = len
         then `Maybe i
         else
           if S.get arr ofs = str.[i]
           then cmp arr ~ofs:(ofs + 1) ~i:(i + 1)
           else `No
     in
     let ret ofs_after =
       let () = fdbg "probe_string: len=%i, dropping %i"
         (S.length arr) ofs_after in
       ie_doneM () (Chunk (S.drop ofs_after arr))
     in
     let rec it_first_step arr ~ofs ~i
      : option (IO.m (iteratee char unit * sl char)) =
       match cmp arr ~ofs ~i with
       [ `Yes ofs_after -> Some (ret ofs_after)
       | `No -> None
       | `Maybe i ->
           let () = fdbg "probe: cont from first step" in
           Some (ie_contM & it_step ~i)
       ]
     and it_step ~i s =
       match s with
       [ EOF eopt ->
           ie_errorMsl
             (match eopt with [ None -> End_of_file | Some e -> e ])
             (Sl.one s)
       | Chunk arr ->
           match cmp arr ~ofs:0 ~i with
           [ `Yes ofs_after -> ret ofs_after
           | `Maybe i -> ie_contM (it_step ~i)
           | `No -> ie_errorMsl Not_found (Sl.one s)
           ]
       ]
     in
       it_first_step arr ~ofs ~i:0
;


(* returns last n items from stream *)
value it_last
 : int -> iteratee 'el (list 'el)
 = fun n ->
     let rec step q s =
       match s with
       [ EOF _ ->
           let r =
             (List.rev
               (Queue.fold
                  (fun acc el -> [el :: acc])
                  []
                  q
               )
             )
           in
           let () = assert (List.length r <= n) in
           ie_doneM r s
       | Chunk arr ->
           let len = S.length arr in
           let () =
             if len >= n
             then
               ( Queue.clear q
               ; let arr_last = S.drop (len - n) arr in
                 let () = assert (S.length arr_last = n) in
                 S.iter (fun el -> Queue.add el q) arr_last
               )
             else
               ( S.iter
                   (fun el ->
                      ( Queue.push el q
                      ; if Queue.length q > n
                        then ignore (Queue.take q)
                        else ()
                      )
                   )
                   arr
               )
           in
             ie_contM (step q)
       ]
     in
       ie_cont (step (Queue.create ()))
;


end
;  (* `Make' functor *)



module I_Pure = Make(Pure_IO);

exception Parse_string_not_full;

(* parses string and ensures that the whole string is fed to iteratee,
   otherwise returns [`Error Parse_string_not_full]. *)
value parse_string_full
 : I_Pure.iteratee char 'a -> string -> [= `Ok of 'a | `Error of exn ]
 = fun it str ->
     let open I_Pure in
     Pure_IO.runIO &
     (enum_string str
       (it >>= fun r ->
        peek >>= fun
        [ Some _ -> throw_err Parse_string_not_full
        | None -> return r
        ]
       )
      >>% run
     )
     
;









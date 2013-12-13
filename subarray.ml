open It_Ops
;

module C
 :
  sig
    type t 'a = private { arr : array 'a; ofs : int; len : int };
    value empty : t 'a;
    value mk : ~arr:array 'a -> ~ofs:int -> ~len:int -> t 'a;
  end
 =
  struct
    type t 'a = { arr : array 'a; ofs : int; len : int };
    value empty = { arr = [||]; ofs = 0; len = 0 };
    value mk ~arr ~ofs ~len =
      if ofs < 0 || len < 0
         || ofs + len > Array.length arr
      then
        failwith "Subarray.C.mk: bad indexes"
      else
        if len = 0
        then empty
        else { arr=arr; ofs=ofs; len=len }
    ;
  end
;

type t 'a = C.t 'a == private { arr : array 'a; ofs : int; len : int };

value length s = s.len
;

value get s i =
  if i < 0 || i >= s.len
  then invalid_arg "Subarray.get"
  else s.arr.(s.ofs + i)
;

value empty = C.empty;

open C;

value is_empty s = (0 = length s);

(* copy chars from str[ofs..ofs+len-1] into arr. *)
value replace_with_substring arr str ofs len =
  let () = assert (ofs >= 0 && len >= 0 && ofs+len <= Array.length arr
                   && ofs+len <= String.length str) in
  let () =
    for i = 0 to len-1 do
      ( arr.(i) := str.[ofs + i]
      )
    done
  in
  C.mk ~arr ~ofs:0 ~len
;

value of_string str =
  let len = String.length str in
  replace_with_substring (Array.make len '\x00') str 0 len
;

value of_array arr = C.mk ~arr ~ofs:0 ~len:(Array.length arr)
;

value of_array_sub arr ofs len =
  C.mk ~arr ~ofs ~len
;

value of_list lst = of_array (Array.of_list lst)
;

value of_elem el = C.mk ~arr:[|el|] ~ofs:0 ~len:1
;

type dir = [ L | R ];

value fold dir func init s =
  let (i, stp) =
    match dir with
    [ L -> (s.ofs, 1)
    | R -> (s.ofs + s.len - 1, -1)
    ]
  in
    inner ~i ~left:s.len ~cur:init
    where rec inner ~i ~left ~cur =
      if left = 0
      then
        cur
      else
        inner
          ~i:(i + stp)
          ~left:(left - 1)
          ~cur:(func cur s.arr.(i))
;

value iter
 : ('a -> unit) -> t 'a -> unit
 = fun f s ->
     fold L (fun () x -> let () = f x in ()) () s
;


value to_list s =
  fold R
    (fun acc elem -> [elem :: acc])
    []
    s
;

value rec to_string_loop arr str sub_ofs str_ofs left =
  if left = 0
  then
    str
  else
    ( str.[str_ofs] := arr.(sub_ofs)
    ; to_string_loop arr str (sub_ofs + 1) (str_ofs + 1) (left - 1)
    )
;

value to_string s =
  to_string_loop s.arr (String.make s.len '\x00') s.ofs 0 s.len
;

value append_to_list_rev s lst =
  fold L
    (fun acc elem -> [elem :: acc])
    lst
    s
;

value get_first_item s =
  if s.len = 0
  then None
  else Some s.arr.(s.ofs)
;

value destruct_first_item s =
  if s.len = 0
  then None
  else some &
    (s.arr.(s.ofs), C.mk ~arr:s.arr ~ofs:(s.ofs+1) ~len:(s.len-1))
;

value sub s ~ofs ~len =
  if ofs < 0 || len < 0 || ofs > s.len - len
  then invalid_arg "Subarray.sub"
  else
    if len = s.len
    then s
    else C.mk ~arr:s.arr ~ofs:(s.ofs + ofs) ~len:len
;

value split_at i s =
  if i < 0 then invalid_arg "Subarray.split_at" else
  let i = min i s.len in
  ( sub s ~ofs:0 ~len:i
  , sub s ~ofs:i ~len:(s.len - i)
  )
;

value drop i s =
  if i < 0 then invalid_arg "Subarray.drop" else
  let (_s1, s2) = split_at i s  (* could be optimized *)
  in
    s2
;


(* +
   [break pred s] applied to a predicate [pred] and a "substring" [s],
   returns a tuple where first element is longest prefix
   (possibly empty) of [s] of elements that do not satisfy [pred]
   and second element is the remainder of the list.
*)

value break pred s =
  let rec len_no_match i =
    if i = s.len
    then i
    else 
      if pred s.arr.(s.ofs + i)
      then i
      else len_no_match (i+1)
  in
  let prefix_len = len_no_match 0 in
  split_at prefix_len s
;


(* +
   [break_limit ~limit pred s] looks at first [limit] elements.
   If found element matching [pred], then [`Found (prefix, rest)]
   returned.  If the limit is hit, then [`Hit_limit] returned
   (so, if it is ok for you, use [split_at limit s] to get pieces).
   If the end of chunk is hit, then [`Hit_end] returned (and
   the whole [s] does not match [pred]).
   If [limit = length s] and no elements found, then [`Hit_limit]
   returned (limit has more priority than chunk's end).
*)

value break_limit ~limit pred s =
  inner 0
  where rec inner i =
    if i = limit
    then
      `Hit_limit
    else
      if i = s.len
      then
        `Hit_end
      else
        if pred s.arr.(s.ofs + i)
        then
          `Found (split_at i s)
        else
          inner (i + 1)
;


(* +
   [drop_while pred s] returns the remaining "substring" of [s]
   which remains after cutting off the longest prefix (possibly empty)
   of [s] of elements that satisfy predicate [pred].
 *)

value drop_while pred s =
  let (_s1, s2) = break (not % pred) s  (* could be optimized *)
  in
    s2
;

value is_empty s = (s.len = 0)
;

value buffer_add buf s =
  Buffer.add_string buf (to_string s)
;

value map f s =
  of_array &
  Array.map f &
  Array.init s.len &
  fun i -> s.arr.(s.ofs + i)
;

value copy s =
  mk ~arr:(Array.sub s.arr s.ofs s.len) ~ofs:0 ~len:s.len
;


(* concatenate previously splitted pieces (b follows a) *)

value concat_splitted a b =
  match (a.len, b.len) with
  [ (0, _) -> b
  | (_, 0) -> a
  | (alen, blen) ->
      if a.arr != b.arr then invalid_arg "Subarray.concat: arr" else
      if a.ofs + alen <> b.ofs then invalid_arg "S.concat: ranges" else
      C.mk ~arr:a.arr ~ofs:a.ofs ~len:(alen + blen)
  ]
;

value blit_to_array ~src ~src_ofs ~dst ~dst_ofs ~len =
  if len < 0
  then invalid_arg "Subarray.blit: len"
  else
  if src_ofs < 0 || src_ofs > src.len - len
  then invalid_arg "Subarray.blit: source"
  else
  if dst_ofs < 0 || dst_ofs > Array.length dst - len
  then invalid_arg "Subarray.blit: destination"
  else
    Array.blit
      src.arr (src_ofs + src.ofs)
      dst      dst_ofs
      len
;

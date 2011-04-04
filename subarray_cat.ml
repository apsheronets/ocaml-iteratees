open It_Ops
;

module S = Subarray
;

type t 'a = array (Subarray.t 'a)
;

value (array_filter : ('a -> bool) -> array 'a -> array 'a) pred arr =
  let bads = Array.fold_left
    (fun count x -> count + if not & pred x then 1 else 0)
    0
    arr
  in
  if bads = 0
  then arr
  else
    let new_len = Array.length arr - bads in
    if new_len = 0
    then [| |]
    else
      let res = Array.make new_len arr.(0)
      and i = ref 0 in
      ( Array.iter
          (fun x ->
             if pred x
             then
               ( res.(i.val) := x
               ; incr i
               )
             else ()
          )
          arr
      ; res
      )
;

value make_of_array arr =
  array_filter (fun s -> S.length s <> 0) arr
;

value make lst = make_of_array & Array.of_list lst
;

value (append_array : array 'a -> 'a -> array 'a) src s =
  let src_len = Array.length src in
  Array.init (src_len + 1) & fun i ->
    if i = src_len
    then s
    else src.(i)
;

value append src s =
  make_of_array & append_array src s
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

value sub_copy_out ?(ofs=0) ?len sc =
  let len =
    match len with
    [ None -> length sc - ofs
    | Some len -> len
    ]
  in
  let sc_len = length sc in
  if ofs < 0 || len < 0 || ofs+len > sc_len
  then invalid_arg "Subarray_cat.sub_copy_out"
  else
  S.of_array & Array.init len (fun i -> get sc (ofs+i))
;

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

value (snoc_array : array 'a -> 'a -> array 'a) sc s =
  let sc_len = Array.length sc in
  Array.init (sc_len + 1) & fun i ->
    if i = sc_len
    then s
    else sc.(i)
;

value snoc sc s =
  make_of_array & snoc_array sc s
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


value empty_array = [| |]
;


value rec sub_copy__loop ~to_skip ~to_copy ~res ~res_i ~sc_i ~sc =
  if to_copy = 0
  then
    ( assert
        (res != empty_array && to_skip = 0 && to_copy = 0 &&
         res_i = Array.length res
        )
    ; res
    )
  else
    let s = sc.(sc_i) in
    let s_len = S.length s in
    if (* s_len = 0 || *) to_skip >= s_len
       (* ^^^ included in ^^^ as a logic coincidence *)
    then
      sub_copy__loop
        ~to_skip:(to_skip - s_len) ~to_copy ~res ~res_i ~sc_i:(sc_i + 1)
        ~sc
    else
      if to_skip = 0
      then
        (* blitting *)
        let s_copy_len = min to_copy s_len in
        sub_copy__copy
          ~res ~res_i ~s ~ofs:0 ~len:s_copy_len
          ~sc_i ~to_copy ~sc
      else
        (* here: 0 < to_skip < s_len:
           skipping part of s, copying other part
         *)
        let s_copy_ofs = to_skip in
        let s_avail = s_len - s_copy_ofs in
        let s_copy_len = min to_copy s_avail in
        sub_copy__copy
          ~res ~res_i ~s ~ofs:s_copy_ofs ~len:s_copy_len
          ~sc_i ~to_copy ~sc

and sub_copy__copy ~res ~res_i ~s ~ofs ~len ~sc_i ~to_copy ~sc =
  let res =
    if res == empty_array
    then
      let init_item = S.get s ofs in
      Array.make to_copy init_item
      (* no items were copied, so to_copy == all items we need *)
    else
      res
  in
  ( S.blit_to_array
      ~src:s   ~src_ofs:ofs
      ~dst:res ~dst_ofs:res_i
      ~len
  ;
    (* copy can pass sc_i out of sc to loop when to_copy = 0 *)
    sub_copy__loop
      ~to_skip:0 ~to_copy:(to_copy - len) ~res ~res_i:(res_i + len)
      ~sc_i:(sc_i + 1) ~sc
  )
;

value sub_copy_out_to_array ~ofs ~len sc =
  (* here: checked that ofs..len is a valid subarray of sc. *)
  if len = 0
  then empty_array
  else sub_copy__loop
    ~to_skip:ofs ~to_copy:len ~res:empty_array ~res_i:0 ~sc ~sc_i:0
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
  S.of_array & sub_copy_out_to_array ~ofs ~len sc
;

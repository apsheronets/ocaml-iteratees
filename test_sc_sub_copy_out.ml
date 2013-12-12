value () = Random.init 2
;

value res f =
  try `Ok (f ()) with [ e -> `Error e ]
;

value cmp_res f1 f2 =
  (res f1) = (res f2)
;


module SC = Subarray_cat
;

module S = Subarray
;

open It_Ops
;

value old_sub_copy_out ~ofs ~len sc =
  let sc_len = SC.length sc in
  if ofs < 0 || len < 0 || ofs+len > sc_len
  then invalid_arg "Subarray_cat.sub_copy_out"
  else
  S.of_array & Array.init len (fun i -> SC.get sc (ofs+i))
;

value new_sub_copy_out = SC.sub_copy_out
;

(*******************)

value random_subarray () =
  let arr_len = Random.int 500 in
  let arr = Array.init arr_len (fun _ -> Random.int 10000) in
  let subarr_ofs = Random.int (arr_len + 1) in
  let arr_avail = arr_len - subarr_ofs in
  let subarr_len = Random.int (arr_avail + 1) in
  S.of_array_sub arr subarr_ofs subarr_len
;

value random_sc () =
  let count = Random.int 5 in
  SC.make & Array.to_list & Array.init count (fun _ -> random_subarray ())
;

value test () =
  for _sc's = 0 to 10000 do
    let sc = random_sc () in
    let sc_len = SC.length sc in
    for _tests = 0 to 10000 do
      let ofs = -3 + Random.int (sc_len + 6)
      and len = -3 + Random.int (sc_len + 6) in
      if cmp_res
        (fun () -> old_sub_copy_out ~ofs ~len sc)
        (fun () -> new_sub_copy_out ~ofs ~len sc)
      then ()
      else failwith "bad"
    done
  done
;


value bench () =
  for _sc's = 0 to 0 do
    let sc = random_sc () in
    let sc_len = SC.length sc in
    for _tests = 0 to 10000000 do
      let ofs = -3 + Random.int (sc_len + 6)
      and len = -3 + Random.int (sc_len + 6) in
      ignore (res
        (fun () -> old_sub_copy_out ~ofs ~len sc)
(*
        (fun () -> new_sub_copy_out ~ofs ~len sc)
*)
      )
    done
  done
;


value () = (bench (); Printf.printf "alloc = %f\n" (Gc.allocated_bytes ()))
;

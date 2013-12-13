(* concatenated subarrays holding values of type ['a] *)
type t 'a;

value make : list (Subarray.t 'a) -> t 'a;

(* [length sc] returns count of elements stored in all subarrays
   contained in [sc]
*)
value length : t 'a -> int;

(* [get sc i] gets item from concatenated subarrays [sc]
   by global index [i] (from [0] to [length sc - 1]).
   Raises [Invalid_argument "Subarray_cat.get"] when
   [i] is out of bounds. *)
value get : t 'a -> int -> 'a;

(* [sub_copy_out sc ~ofs ~len] copies items from
   global offset [ofs] and length [len] from concatenated
   subarrays [sc] into freshly created subarray. *)
value sub_copy_out : ?ofs:int -> ?len:int -> t 'a -> Subarray.t 'a;

(* [snoc s] appends subarray [s] to the end of
   concatenated subarrays [sc].
*)
value snoc : t 'a -> Subarray.t 'a -> t 'a;

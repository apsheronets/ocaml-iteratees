open Ops

module Stream =
  struct
    include Stream

    let get_opt s = try Some (next s) with Failure -> None

    let map f s = from & fun _ ->
      match get_opt s with None -> None | Some x -> Some (f x)

    let map2 ?(strict=true) f s1 s2 = from & fun _ ->
      match get_opt s1, get_opt s2 with
      | None, None -> None
      | Some _, None | None, Some _ ->
          if strict then raise Failure else None
      | Some x, Some y -> Some (f x y)

    let ints ?(nstep=1) ?(nend=max_int) nstart =
      let cur = ref nstart in
      from & fun _ ->
        let r = !cur in
        if r > nend
        then None
        else
          ( cur := !cur + nstep;
            Some r
          )

    let from_repeat f x =
      from & fun _ -> Some (f x)


  end



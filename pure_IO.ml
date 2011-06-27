(* Pure "function name" is raised when the IO-function is called *)

exception Pure of string
;

    type m +'a = [= `Ok of 'a | `Error of exn ];
    value return x = `Ok x;
    value bind f m =
      match m with
      [ `Ok a -> f a
      | (`Error _) as me -> me
      ]
    ;
    value bind_rev m f =
      match m with
      [ `Ok a -> f a
      | (`Error _) as me -> me
      ]
    ;

    value error e = `Error e;

    value pu n = error (Pure n);


    value catch f handler =
      try
        match f () with
        [ (`Ok _) as a -> a
        | `Error e ->
            try
              handler e
            with
            [ ee -> `Error ee ]
        ]
      with
      [ e -> handler e ]
    ;

    type output_channel = unit;
    value stdout = ();
    value write () (_ : string) = pu "write";

    type input_channel = unit;
    value open_in (_ : string) = pu "open_in";
    value close_in () = pu "close_in";
    value read_into () (_:string) (_:int) (_:int) = pu "read_into";

    value runIO (x : m 'a) = (x :> [= `Ok of 'a | `Error of exn]);

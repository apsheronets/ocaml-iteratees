value script = "\
#use \"topfind\";;
#camlp4r;;
#require \"monad_io\";
#directory \"_build\";
#load \"it_Types.cmo\";
#load \"direct_IO.cmo\";
module It_IO = Direct_IO.Direct_IO;
#load \"dbg.cmo\";
#load \"it_Ops.cmo\";
#load \"subarray.cmo\";
#load \"subarray_cat.cmo\";
#load \"iteratees.cmo\";
print_newline ();
module Result = Iteratees.Make(It_IO);
";


value input_line_opt inch =
  try Some (input_line inch) with [ End_of_file -> None ]
;


value replace_lines =
  [ ( "      Iteratees.Make(It_IO).stream 'a =="
    , ""
    )
  ; ( "        type output_channel = It_IO.output_channel;"
    , "        type output_channel;"
    )
  ; ( "        type input_channel = It_IO.input_channel;"
    , "        type input_channel;"
    )
  ; ( "        type m 'a = It_IO.m 'a;"
    , "        type m +'a;"
    )
  ; ( "          Iteratees.Make(It_IO).Subarray.t 'a == private"
    , "          private"
    )
  ; ( "          Iteratees.Make(It_IO).S.t 'a == private"
    , "          private"
    )
  ; ( "      Iteratees.Make(It_IO).iteratee 'a 'b =="
    , ""
    )
  ; ( "        type uchar = Iteratees.Make(It_IO).UTF8.uchar;"
    , "        type uchar = private int;"
    )
  ; ( "              Iteratees.Make(It_IO).S.C.t 'a == private"
    , "              private"
    )
  ; ( "              Iteratees.Make(It_IO).Subarray.C.t 'a == private"
    , "              private"
    )
  ]
;

value replace_opttype line =
  for i = 0 to String.length line - 2
  do
    if line.[i] = '~' && line.[i + 1] = '?'
    then
      line.[i] := ' '
    else ()
  done
;


value list_assoc_opt k m = try Some (List.assoc k m) with [Not_found -> None];

value replace_line line =
  let res =
    match list_assoc_opt line replace_lines with
    [ None -> line
    | Some r -> r
    ]
  in
    ( replace_opttype res
    ; res
    )
;



value read_out inch =
  let outch = stdout in
  let () = set_binary_mode_out outch True in
  let out line = Printf.fprintf outch "%s\n%!" line in
  let err msg = failwith msg in
  loop `Before
  where rec loop mode =
    match (mode, input_line_opt inch) with
    [ (`Before, None) -> err "sig not found"
    | (`Before, Some "# module Result :") ->
        let (_ : string) = input_line inch in
        ( out "module type IT"
        ; out " ="
        ; out "  sig"
        ; loop `Running
        )
    | (`Before, Some _) -> loop mode
    | (`Running, None) -> err "sig end not found"
    | (`Running, Some ("  end" as line)) ->
        ( out line
        ; out ";"
        ; loop `After
        )
    | (`Running, Some line) ->
         ( out (replace_line line)
         ; loop mode
         )
    | (`After, Some _) -> loop mode
    | (`After, None) -> ()
    ]
;


value dev_null = if Sys.os_type = "Win32" then "NUL" else "/dev/null"
;


value main () =
  let (inch, outch) = Unix.open_process
    (Printf.sprintf "ocaml 2> %s" dev_null) in
  ( output_string outch script
  ; close_out outch
  ; read_out inch
  )
;


value () = main ()
;

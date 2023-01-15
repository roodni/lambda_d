open Lambda_d

let put_scripts_from_exdef path =
  let channel = open_in path in
  let lexbuf = Lexing.from_channel channel in
  let figures = Deflang.load_figures lexbuf in
  let deflist =
    List.map Deflang.figure_to_definitions figures
    |> List.concat
  in
  Inference.put_script_deriving_definitions deflist;
;;

let () =
  put_scripts_from_exdef Sys.argv.(1)
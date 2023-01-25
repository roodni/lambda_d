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

let put_scripts_from_def2 path =
  let channel = open_in path in
  let deflist = Deflang.Def2.load channel in
  Inference.put_script_deriving_definitions deflist

let () =
  match Sys.argv with
  | [| _; "-x"; path |] ->
      (* Definition記述DSL *)
      put_scripts_from_exdef path;
  | [| _; defpath; |] ->
      put_scripts_from_def2 defpath;
  | [| _; defpath; _; logpath |] ->
      (* 授業配付プログラム互換 *)
      Inference.cha := open_out logpath;
      put_scripts_from_def2 defpath;
  | _ -> failwith "引数が違う"
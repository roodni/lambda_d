open Lambda_d
(* open Syntax *)

let convert path =
  let channel = open_in path in
  let lexbuf = Lexing.from_channel channel in
  let figures = Deflang.load_figures lexbuf in
  List.iter
    (fun fig ->
      let defs = Deflang.figure_to_definitions fig in
      List.iter
        (fun def ->
          Deflang.Def2.print def;
          print_newline (); )
        defs; )
    figures;
  print_endline "END";
;;

let () =
  convert Sys.argv.(1)
open Printf

open Lambda_d
(* open Syntax *)

let convert path =
  let channel = open_in path in
  let lexbuf = Lexing.from_channel channel in
  let figures =
    try Parser.deflang Lexer.main lexbuf with
    | Lexer.Error | Parser.Error ->
        let Lexing.{ pos_lnum; pos_cnum; pos_bol; _ } = Lexing.lexeme_start_p lexbuf in
        failwith
        @@ sprintf "line %d, col %d: parse error"
            pos_lnum
            (1 + pos_cnum - pos_bol)
  in
  List.iter
    (fun fig ->
      let defs = Deflang.figure_to_definitions fig in
      List.iter
        (fun def ->
          Deflang.print_definition def;
          print_newline (); )
        defs; )
    figures;
  print_endline "END";
;;

let () =
  convert Sys.argv.(1)
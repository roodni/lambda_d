open Lambda_d
open Syntax

let () =
  let path = Sys.argv.(1) in
  let channel =
    if path = "-" then stdin else open_in path
  in
  let lexbuf = Lexing.from_channel channel in
  let term = Parser.term Lexer.main lexbuf in
  print_endline (term_to_string term)
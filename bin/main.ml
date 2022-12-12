open Printf

open Lambda_d
open Syntax


let intaractive () =
  let rec loop () =
    printf "> %!";
    let line =
      try read_line () with
      | End_of_file -> exit 0
    in
    let lexbuf = Lexing.from_string line in
    let term =
      try Some (Parser.main Lexer.main lexbuf) with
      | Parser.Error | Lexer.Error _ -> None
    in
    ( match term with
      | None -> printf "error\n";
      | Some term ->
          print_term term;
          print_newline ();
    );
    loop ()
  in
  loop ()

let fileloader path =
  let channel = open_in path in
  let lexbuf = Lexing.from_channel channel in
  let term =
    try Parser.main Lexer.main lexbuf with
    | Parser.Error | Lexer.Error _ ->
        eprintf "parse error\n";
        exit 1
  in
  print_term term;
  print_newline ();
  close_in channel

let () =
  if Array.length Sys.argv <= 1
    then intaractive ()
    else fileloader Sys.argv.(1)
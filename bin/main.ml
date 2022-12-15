open Printf

open Lambda_d
open Syntax

let string_to_term s =
  let lexbuf = Lexing.from_string s in
  let term =
    try Parser.main Lexer.main lexbuf with
    | Parser.Error | Lexer.Error _ -> raise (Invalid_argument s)
  in
  term
;;

let intaractive () =
  let rec loop () =
    printf "> %!";
    let line =
      try read_line () with
      | End_of_file -> exit 0
    in
    match string_to_term line with
    | term ->
        Term.print term;
        print_newline ();
        loop ()
    | exception Invalid_argument _ ->
       printf "parse error\n";
       loop ()
  in
  loop ()

let fileloader path =
  let channel = open_in path in
  let l1 = input_line channel in
  let l2 = input_line channel in
  let t1 = string_to_term l1 in
  let t2 = string_to_term l2 in
  if Term.alpha_equal t1 t2 then begin
    printf "alpha-equivalent\n";
  end else begin
    printf "NOT alpha-equivalent\n";
  end;
  print_newline ();
  close_in channel

let () =
  if Array.length Sys.argv <= 1
    then intaractive ()
    else fileloader Sys.argv.(1)
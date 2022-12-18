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
  let rec lineloop eq_sets =
    match input_line channel with
    | exception End_of_file -> eq_sets
    | line ->
        let term = string_to_term line in
        let cnt, eq_sets =
          List.fold_left_map
            (fun (cnt: int) (eq_set: Term.t list) ->
              let res = List.map (Judge.alpha_equal2 term) eq_set in
              if List.for_all Fun.id res then (* 同じだった *)
                (cnt + 1, term :: eq_set)
              else if List.for_all not res then (* 違った *)
                (cnt, eq_set)
              else (* 推移律に反する *)
                assert false
            )
            0 eq_sets
        in
        ( match cnt with
          | 0 -> lineloop ([term] :: eq_sets)
          | 1 -> lineloop eq_sets
          | _ -> assert false (* 推移律に反する *)
        )
  in
  let eq_sets = lineloop [] in
  List.iter
    (fun eq_set ->
      printf "{ ";
      List.iteri
        (fun i term ->
          if i > 0 then  printf "\n  ";
          Term.print term;
        )
        (List.rev eq_set);
      printf " }\n\n";
    )
    (List.rev eq_sets)

let () =
  if Array.length Sys.argv <= 1
    then intaractive ()
    else fileloader Sys.argv.(1)
open Printf
open Scanf

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

(* let classify_term path =
  let channel = open_in path in
  let rec lineloop eq_sets =
    match input_line channel with
    | exception End_of_file -> eq_sets
    | line ->
        let term = string_to_term line in
        let cnt, eq_sets =
          List.fold_left_map
            (fun (cnt: int) (eq_set: Term.t list) ->
              let res = List.map (Judge.alpha_equal term) eq_set in
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
          Term.print term; )
        (List.rev eq_set);
      printf " }\n\n"; )
    (List.rev eq_sets)
;; *)

let validate_judgements path =
  let channel = open_in path in
  let ib = Scanning.from_channel channel in
  let tbl = Hashtbl.create 100 in
  let rec input_loop () =
    let index = bscanf ib "%d " Fun.id in
    if index = -1 then raise Exit;
    if Hashtbl.mem tbl index then
      failwith (sprintf "index %d is already used" index);
    let find_judge i =
      match Hashtbl.find_opt tbl i with
      | Some j -> j
      | None -> failwith (sprintf "%d: judgemnt %d not found" index i)
    in
    let rule = bscanf ib "%s " Fun.id in
    let judge_opt =
      let open Judge in
      match rule with
      | "sort" ->
          Some (Judgement.make_sort ())
      | "var" ->
          bscanf ib "%d %s "
            (fun p v ->
              Judgement.make_var (find_judge p) (Named v)
            )
      | "weak" ->
          bscanf ib "%d %d %s "
            (fun p1 p2 v ->
              Judgement.make_weak (find_judge p1) (find_judge p2) (Named v))
      | "form" ->
          bscanf ib "%d %d "
            (fun p1 p2 ->
              Judgement.make_form (find_judge p1) (find_judge p2))
      | "appl" ->
          bscanf ib "%d %d "
            (fun p1 p2 ->
              Judgement.make_appl (find_judge p1) (find_judge p2))
      | "abst" ->
          bscanf ib "%d %d "
            (fun p1 p2 ->
              Judgement.make_abst (find_judge p1) (find_judge p2))
      | "conv" ->
          bscanf ib "%d %d "
            (fun p1 p2 ->
              Judgement.make_conv (find_judge p1) (find_judge p2))
      | "def" ->
          bscanf ib "%d %d %s "
            (fun p1 p2 name ->
              Judgement.make_def (find_judge p1) (find_judge p2) name)
      | "inst" ->
          bscanf ib "%d %d "
            (fun m n ->
              let pre1 = find_judge m in
              let pres = List.init n (fun _ -> bscanf ib "%d " find_judge) in
              bscanf ib "%d "
                (fun p -> Judgement.make_inst pre1 pres p) )
      | "cp" ->
          bscanf ib "%d " (fun p -> find_judge p |> Option.some)
      | "sp" ->
          bscanf ib "%d %d "
            (fun p l ->
              let j = find_judge p in
              let xl, tl =
                try List.nth (List.rev j.context) l with
                | Invalid_argument _ -> failwith (sprintf "%d: invalid l=%d" index l)
              in
              Judgement.{
                definitions = j.definitions;
                context = j.context;
                proof = Var xl;
                prop = tl;
              } |> Option.some )
      | _ -> failwith (sprintf "%d: unimplemented rule '%s'" index rule)
    in
    match judge_opt with
    | None -> failwith (sprintf "%d: invalid judgement" index)
    | Some judge ->
        Hashtbl.add tbl index judge;
        printf "%d:\t" index;
        Judge.Judgement.print judge;
        print_newline ();
        input_loop ()
  in
  try input_loop () with Exit -> ()
;;

let () =
  if Array.length Sys.argv <= 1
    then intaractive ()
    else validate_judgements Sys.argv.(1)
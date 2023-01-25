open Printf
open Scanf

open Lambda_d
open Syntax
open Conv

(* 型チェック *)
let validate_judgements path =
  let channel = open_in path in
  let ib = Scanning.from_channel channel in
  let tbl = Hashtbl.create 100 in
  let lasti = ref (-1) in
  let rec input_loop () =
    let index = bscanf ib "%d " Fun.id in
    if index = -1 then raise Exit;
    lasti := index;
    if Hashtbl.mem tbl index then
      failwith (sprintf "index %d is already used" index);
    let find_judge i =
      match Hashtbl.find_opt tbl i with
      | Some j -> j
      | None -> failwith (sprintf "%d: judgemnt %d not found" index i)
    in
    let rule = bscanf ib "%s " Fun.id in
    eprintf "%d:\t %s\n%!" index rule;
    let judge_opt =
      match rule with
      | "sort" ->
          Some (Judgement.make_sort ())
      | "var" ->
          bscanf ib "%d %s "
            (fun p v ->
              Judgement.make_var (find_judge p) (Var.named v)
            )
      | "weak" ->
          bscanf ib "%d %d %s "
            (fun p1 p2 v ->
              Judgement.make_weak (find_judge p1) (find_judge p2) (Var.named v))
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
      | "defpr" ->
          bscanf ib "%d %d %s "
            (fun p1 p2 name ->
              Judgement.make_def_prim (find_judge p1) (find_judge p2) name)
      | "inst" | "instpr" ->
          bscanf ib "%d %d "
            (fun m n ->
              let pre1 = find_judge m in
              let pres = List.init n (fun _ -> bscanf ib "%d " find_judge) in
              bscanf ib "%d "
                (fun p -> Judgement.make_inst ~prim:(rule = "instpr") pre1 pres p) )
      | "cp" ->
          bscanf ib "%d " (fun p -> find_judge p |> Option.some)
      | "sp" ->
          bscanf ib "%d %d "
            (fun p l ->
              match find_judge p with
              | { definitions; context; proof=Star; prop=Square } ->
                  let xl, tl =
                    try List.nth (List.rev context) l with
                    | Invalid_argument _ -> failwith (sprintf "%d: invalid l=%d" index l)
                  in
                  Judgement.{
                    definitions = definitions;
                    context = context;
                    proof = Var xl;
                    prop = tl;
                  } |> Option.some
              | _ -> None )
      | _ -> failwith (sprintf "%d: unimplemented rule '%s'" index rule)
    in
    match judge_opt with
    | None -> failwith (sprintf "%d: invalid judgement" index)
    | Some judge ->
        Hashtbl.add tbl index judge;
        printf "%d:\t" index;
        Judgement.print judge;
        print_newline ();
        if rule = "def" || rule = "defpr" then begin
          let def = Defs.last judge.definitions in
          printf " (def)\t";
          Definition.print def;
          printf "\n";
        end;
        input_loop ()
  in
  try input_loop (); with Exit -> ();
  let last_judge = Hashtbl.find tbl !lasti in
  Defs.reportnf last_judge.definitions
;;

let () =
  match Sys.argv with
  | [| _; path |]
  | [| _; _; path |] -> (* 授業配付プログラムとの互換性 *)
      validate_judgements path
  | _ -> failwith "引数が違う"
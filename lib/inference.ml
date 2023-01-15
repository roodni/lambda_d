open Printf

open Syntax
open Judge

let (let*) = Option.bind
let getopt f = function
  | Some x -> x
  | None -> f ()

let rec get_type defs ctx term =
  match term with
  | Term.Star -> Some Term.Square
  | Square -> assert false (* not implemented *)
  | Var v ->
      let* t = List.assoc_opt v ctx in
      Some (normal_form defs t)
  | App (m, n) -> begin
      let* p = get_type defs ctx m in
      match p with
      | Pai (z, _, b) ->
          normal_form defs (assign [(z, n)] b)
          |> Option.some
      | _ -> None
    end
  | Lambda (x, a, b) | Pai (x, a, b) -> begin
      let z = Var.gen x in
      let b = assign [(x, Var z)] b in
      match term with
      | Lambda _ ->
          let* bty = get_type defs ((z, a) :: ctx) b in
          normal_form defs (Pai (z, a, bty))
          |> Option.some
      | Pai _ -> get_type defs ctx b
      | _ -> assert false
    end
  | Const (name, tl) -> begin
      let* def = Definition.lookup name defs in
      let* ass =
        try
          List.map2 (fun (x, _) t -> (x, t)) def.context (List.rev tl)
          |> Option.some
        with Invalid_argument _ -> None
      in
      normal_form defs (assign ass def.prop) |> Option.some
    end


let line = ref 0
let put_line s =
  printf "%d %s\n" !line s;
  incr line;
  !line - 1

(* ctx = x1:A1, ..., xn:An とする
   `Star ->  defs; ctx |- *: @ となる行番号
   `Var xi -> defs; ctx |- xi: Ai となる行番号
*)
type var_to_line = [`Star | `Var of Var.t] -> int

(* asc は defs; ctx |- a: s に対応する行番号
   以下の判断
   defs; ctx, x:a |- *: @
   defs; ctx, x:a |- xi: Ai
   defs; ctx, x:a |- x: a
   を導出するスクリプトをそれぞれ出力し、
   新しい環境(ctx, x:a)と該当する行番号のペアを返す
*)
let put_script_adding_context ctx (f: var_to_line) x a asc
    : Context.t * var_to_line =
  let starsc =
    put_line @@ sprintf "weak %d %d %s"
      (f `Star)
      asc
      (Var.to_string x)
  in
  let varscs =
    List.fold_left
      (fun dict (xi, _) ->
        let sc =
          put_line @@ sprintf "weak %d %d %s"
            (f (`Var xi))
            asc
            (Var.to_string x)
        in
        (xi, sc) :: dict
      )
      [] ctx
  in
  let xsc =
    put_line @@ sprintf "var %d %s" asc (Var.to_string x)
  in
  let ctx' = (x, a) :: ctx in
  let f' = function
    | `Star -> starsc
    | `Var v when v = x -> xsc
    | `Var v -> List.assoc v varscs
  in
  (ctx', f')

(* 判断
   defs; ctx |- term: ?
   を導出するスクリプトを出力し、さらに該当する行番号を返す
*)
let rec put_script defs ctx (f: var_to_line) term =
  let err msg () =
    printf "導出に失敗した:\n";
    Definition.print_all defs;
    printf ";\n";
    Context.print ctx;
    printf " |- ";
    Term.print term;
    printf "\n%s\n" msg;
    failwith msg
  in
  match term with
  | Term.Star -> f `Star
  | Var v -> f (`Var v)
  | Square -> assert false (* not implemented *)
  | App (m, n) ->
      let mty = get_type defs ctx m |> getopt (err "fail1") in
      let nty = get_type defs ctx n |> getopt (err "fail2") in
      let msc = put_script defs ctx f m in
      let mtysc = put_script defs ctx f mty in
      let mconvsc =
        put_line @@ sprintf "conv %d %d" msc mtysc
      in
      let nsc = put_script defs ctx f n in
      let ntysc = put_script defs ctx f nty in
      let nconvsc =
        put_line @@ sprintf "conv %d %d" nsc ntysc
      in
      put_line @@ sprintf "appl %d %d" mconvsc nconvsc
  | Pai (x, a, b) ->
      let is_x_dup = List.exists (fun (v, _) -> v = x) ctx in
      let x, b =
        if not is_x_dup then (x, b)
        else
          let z = Var.gen x in
          let b' = assign [(x, Var z)] b in
          (z, b')
      in
      let asc = put_script defs ctx f a in
      let ctx', f' = put_script_adding_context ctx f x a asc in
      let bsc = put_script defs ctx' f' b in
      put_line @@ sprintf "form %d %d" asc bsc
  | Lambda (x, a, m) ->
      let is_x_dup = List.exists (fun (v, _) -> v = x) ctx in
      let x, m =
        if not is_x_dup then (x, m)
        else
          let z = Var.gen x in
          let m' = assign [(x, Var z)] m in
          (z, m')
      in
      let asc = put_script defs ctx f a in
      let ctx', f' = put_script_adding_context ctx f x a asc in
      let msc = put_script defs ctx' f' m in
      let b =
        get_type defs ctx' m
        |> getopt (err @@ sprintf "%s の型が得られなかった" (Term.to_string m))
      in
      let bsc = put_script defs ctx' f' b in
      let mconvsc =
        put_line @@ sprintf "conv %d %d" msc bsc
        (* put_scriptが型を返すようにすればここのconvを省けるような気がする *)
      in
      let paisc = put_script defs ctx f (Pai (x, a, b)) in
      put_line @@ sprintf "abst %d %d" mconvsc paisc
  | Const (name, ul) ->
      let defi, def = Definition.lookupi name defs |> getopt (err "fail4") in
      let ctx_and_args =
        (* 定義のコンテキストの各バインディング と 実引数 の組のリスト
           順番は実引数に従う
        *)
        try List.map2 (fun b u -> (b, u)) (List.rev def.context) ul
        with Invalid_argument _ -> err "fail5" ();
      in
      let ass =
        List.map (fun ((x, _), u) -> (x, u)) ctx_and_args
      in
      let scripts =
        List.map
          (fun ((_, a), u) ->
            let usc = put_script defs ctx f u in
            let ty = assign ass a in
            let tysc = put_script defs ctx f ty in
            put_line @@ sprintf "conv %d %d" usc tysc
          )
          ctx_and_args
      in
      put_line @@ sprintf "inst %d %s"
        (f `Star)
        ([List.length scripts] @ scripts @ [defi]
          |> List.map string_of_int
          |> String.concat " " )

let put_script_deriving_definitions deflist =
  let sortsc = put_line "sort" in
  List.fold_left
    (fun (defs, basesc) (def: Definition.t) ->
      (* まず定義のコンテキストから*と各変数に対する判断を構築する *)
      let ctx, f =
        List.fold_left
          (fun (ctx, f) (x, a) ->
            let asc = put_script defs ctx f a in
            let ctx', f' = put_script_adding_context ctx f x a asc in
            (ctx', f')
          )
          ([], (function `Star -> basesc | _ -> assert false))
          (List.rev def.context)
      in
      (* 定義を追加する *)
      let defsc =
        match def.proof with
        | None ->
            let propsc = put_script defs ctx f def.prop in
            put_line @@ sprintf "defpr %d %d %s" basesc propsc def.name
        | Some proof ->
            let proofsc = put_script defs ctx f proof in
            let propsc = put_script defs ctx f def.prop in
            let convsc =
              put_line @@ sprintf "conv %d %d" proofsc propsc
            in
            put_line @@ sprintf "def %d %d %s" basesc convsc def.name
      in
      (def :: defs, defsc)
    )
    ([], sortsc) deflist
  |> ignore;
  print_endline "-1";
;;
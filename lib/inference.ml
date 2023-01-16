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
      let is_x_dup = List.exists (fun (v, _) -> v = x) ctx in
      let z, b =
        if not is_x_dup then (x, b)
        else
          let z = Var.gen x in
          (z, assign [(x, Var z)] b)
      in
      let ctx = (z, a) :: ctx in
      match term with
      | Lambda _ ->
          let* bty = get_type defs ctx b in
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


let cha = ref stdout
let line = ref 0
let put_line s =
  fprintf !cha "%d %s\n" !line s;
  incr line;
  !line - 1


module Memo = struct
  type t = (Context.t * Term.t, (Term.t * int) list) Hashtbl.t

  let create sortsc : t =
    let tbl = Hashtbl.create 100000 in
    Hashtbl.add tbl ([], Term.Star) [(Term.Square, sortsc)];
    tbl

  let find (tbl: t) ctx proof =
    try Hashtbl.find tbl (ctx, proof)
    with Not_found -> []

  let find_with_prop (tbl: t) ctx proof prop =
    let l = find tbl ctx proof in
    List.assoc_opt prop l

  let find_any (tbl: t) ctx proof =
    match find tbl ctx proof with
    | (_, sc) :: _ -> Some sc
    | _ -> None

  let add tbl ctx proof prop sc =
    let l = find tbl ctx proof in
    Hashtbl.add tbl (ctx, proof) ((prop, sc) :: l)
end


(* 判断
   defs; ctx |- term: ?
   を導出するスクリプトを出力し、さらに該当する行番号を返す
*)
let rec put_script_conv memo defs ctx term ty =
  let sc = put_script memo defs ctx term in
  match ty with
  | Term.Square -> sc
  | _ ->
      let tysc = put_script memo defs ctx ty in
      put_line @@ sprintf "conv %d %d" sc tysc

and put_script memo defs ctx term =
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
  match Memo.find_any memo ctx term with
  | Some sc -> sc
  | None ->
      let script_line =
        match term with
        | Term.Star -> begin
            match ctx with
            | (x, c) :: ctx' ->
                let asc = put_script memo defs ctx' term in
                let csc = put_script memo defs ctx' c in
                put_line @@ sprintf "weak %d %d %s" asc csc (Var.to_string x)
            | [] -> assert false (* このケースはmemoに入っているはず *)
          end
        | Var v -> begin
            match ctx with
            | (x, a) :: ctx' when x = v ->
                let asc = put_script memo defs ctx' a in
                put_line @@ sprintf "var %d %s" asc (Var.to_string x)
            | (x, c) :: ctx' ->
                let asc = put_script memo defs ctx' term in
                let csc = put_script memo defs ctx' c in
                put_line @@ sprintf "weak %d %d %s" asc csc (Var.to_string x)
            | [] -> err (sprintf "variable '%s' not found" (Var.to_string v)) ()
          end
        | Square -> err "|- @" ()
        | App (m, n) ->
            let mty = get_type defs ctx m |> getopt (err "fail1") in
            let nty = get_type defs ctx n |> getopt (err "fail2") in
            let msc = put_script_conv memo defs ctx m mty in
            let nsc = put_script_conv memo defs ctx n nty in
            put_line @@ sprintf "appl %d %d" msc nsc
        | Pai (x, a, b) ->
            let is_x_dup = List.exists (fun (v, _) -> v = x) ctx in
            let x, b =
              if not is_x_dup then (x, b)
              else
                let z = Var.gen x in
                let b' = assign [(x, Var z)] b in
                (z, b')
            in
            let asc = put_script memo defs ctx a in
            let ctx' = (x, a) :: ctx in
            let bsc = put_script memo defs ctx' b in
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
            let ctx' = (x, a) :: ctx in
            let b =
              get_type defs ctx' m
              |> getopt (err @@ sprintf "%s の型が得られなかった" (Term.to_string m))
            in
            let msc =
              put_script_conv memo defs ctx' m b
              (* put_scriptが型を返すようにすればここのconvを省けるような気がする *)
            in
            let paisc = put_script memo defs ctx (Pai (x, a, b)) in
            put_line @@ sprintf "abst %d %d" msc paisc
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
            let sortsc = put_script memo defs ctx Term.Star in
            let scripts =
              List.map
                (fun ((_, a), u) ->
                  let ty = assign ass a in
                  put_script_conv memo defs ctx u ty
                )
                ctx_and_args
            in
            put_line @@ sprintf "inst %d %s"
              sortsc
              ([List.length scripts] @ scripts @ [defi]
                |> List.map string_of_int
                |> String.concat " " )
      in
      Memo.add memo ctx term Term.Square script_line;
      script_line
;;

let put_script_deriving_definitions deflist =
  let sortsc = put_line "sort" in
  List.fold_left
    (fun (defs, basesc) (def: Definition.t) ->
      let memo = Memo.create basesc in
      let defsc =
        match def.proof with
        | None ->
            let propsc = put_script memo defs def.context def.prop in
            put_line @@ sprintf "defpr %d %d %s" basesc propsc def.name
        | Some proof ->
            let sc = put_script_conv memo defs def.context proof def.prop in
            put_line @@ sprintf "def %d %d %s" basesc sc def.name
      in
      (def :: defs, defsc)
    )
    ([], sortsc) deflist
  |> ignore;
  fprintf !cha "-1\n"
;;
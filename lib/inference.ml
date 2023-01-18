open Printf

open Syntax
open Judge

let (let*) = Option.bind
let getopt f = function
  | Some x -> x
  | None -> f ()


let cha = ref stdout
let line = ref 0
let put_line s =
  fprintf !cha "%d %s\n%!" !line s;
  incr line;
  !line - 1


module Memo = struct
  type t = (Context.t, (Term.t * Term.t * int) list) Hashtbl.t

  let create sortsc : t =
    let tbl = Hashtbl.create 100000 in
    Hashtbl.add tbl [] [(Term.Star, Term.Square, sortsc)];
    tbl

  let find (tbl: t) ctx =
    try Hashtbl.find tbl ctx
    with Not_found -> []

  let find_with_prop (tbl: t) ctx proof prop =
    find tbl ctx
    |> List.find_map
      (fun (v, ty, sc) ->
        if alpha_equal v proof && alpha_equal ty prop
        then Some sc else None )

  let find_any (tbl: t) ctx proof =
    find tbl ctx
    |> List.find_map
      (fun (v, ty, sc) ->
        if alpha_equal v proof
        then Some (ty, sc) else None
      )

  let add tbl ctx proof prop sc =
    let l = find tbl ctx in
    Hashtbl.add tbl ctx ((proof, prop, sc) :: l)
end


let rec put_script_with_prop memo defs ctx proof prop =
  match Memo.find_with_prop memo ctx proof prop with
  | Some sc -> sc
  | None ->
      let ty, sc = put_script memo defs ctx proof in
      if alpha_equal ty prop then sc
      else
        let _, propsc = put_script memo defs ctx prop in
        let sc = put_line @@ sprintf "conv %d %d" sc propsc in
        Memo.add memo ctx proof prop sc;
        sc

and put_script memo defs ctx term : Term.t * int =
  let err msg () =
    printf "導出に失敗した:\n";
    Defs.print defs;
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
      let derived_type, script_line =
        match term with
        | Term.Star -> begin
            match ctx with
            | (x, c) :: ctx' ->
                let b, asc = put_script memo defs ctx' term in
                let _, csc = put_script memo defs ctx' c in
                let sc =
                  put_line @@ sprintf "weak %d %d %s" asc csc (Var.to_string x)
                in
                (b, sc)
            | [] -> assert false (* このケースはmemoに入っているはず *)
          end
        | Var v -> begin
            match ctx with
            | (x, a) :: ctx' when x = v ->
                let _, asc = put_script memo defs ctx' a in
                let sc = put_line @@ sprintf "var %d %s" asc (Var.to_string x) in
                (a, sc)
            | (x, c) :: ctx' ->
                let b, asc = put_script memo defs ctx' term in
                let _, csc = put_script memo defs ctx' c in
                let sc =
                  put_line @@ sprintf "weak %d %d %s" asc csc (Var.to_string x)
                in
                (b, sc)
            | [] -> err (sprintf "variable '%s' not found" (Var.to_string v)) ()
          end
        | Square -> err "|- @" ()
        | App (m, n) | AppNF (m, n) -> begin
            let mty, msc = put_script memo defs ctx m in
            let x, a, b, msc =
              match mty with
              | Pai (x, a, b) -> (x, a, b, msc)
              | _ -> begin
                  let mtynf = normal_form defs mty |> Term.delete_nf in
                  let msc' = put_script_with_prop memo defs ctx m mtynf in
                  match mtynf with
                  | Pai (x, a, b) -> (x, a, b, msc')
                  | _ -> err (sprintf "%s は適用可能な型ではない" (Term.to_string mty)) ()
                end
            in
            let nsc = put_script_with_prop memo defs ctx n a in
            let ty = assign [(x, n)] b in
            let sc =
              put_line @@ sprintf "appl %d %d" msc nsc
            in
            (ty, sc)
          end
        | Pai (x, a, b) | PaiNF (x, a, b) ->
            let is_x_dup = List.exists (fun (v, _) -> v = x) ctx in
            let x, b =
              if not is_x_dup then (x, b)
              else
                let z = Var.gen x in
                let b' = assign [(x, Var z)] b in
                (z, b')
            in
            let _, asc = put_script memo defs ctx a in
            let ctx' = (x, a) :: ctx in
            let s2, bsc = put_script memo defs ctx' b in
            let sc =
              put_line @@ sprintf "form %d %d" asc bsc
            in
            (s2, sc)
        | Lambda (x, a, m) | LambdaNF (x, a, m) ->
            let is_x_dup = List.exists (fun (v, _) -> v = x) ctx in
            let x, m =
              if not is_x_dup then (x, m)
              else
                let z = Var.gen x in
                let m' = assign [(x, Var z)] m in
                (z, m')
            in
            let ctx' = (x, a) :: ctx in
            let b, msc = put_script memo defs ctx' m in
            let pai = Term.Pai (x, a, b) in
            let _, paisc = put_script memo defs ctx pai in
            let sc = put_line @@ sprintf "abst %d %d" msc paisc in
            (pai, sc)
        | Const (name, ul) | ConstNF (name, ul) ->
            let defi, def = Defs.lookupi name defs |> getopt (err "fail4") in
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
            let _, sortsc = put_script memo defs ctx Term.Star in
            let scripts =
              List.map
                (fun ((_, a), u) ->
                  let ty = assign ass a in
                  let sc = put_script_with_prop memo defs ctx u ty in
                  sc
                )
                ctx_and_args
            in
            let sc =
              put_line @@ sprintf "inst %d %s"
                sortsc
                ([List.length scripts] @ scripts @ [defi]
                  |> List.map string_of_int
                  |> String.concat " " )
            in
            let ty = assign ass def.prop in
            (ty, sc)

      in
      Memo.add memo ctx term derived_type script_line;
      (derived_type, script_line)
;;

let put_script_deriving_definitions deflist =
  let sortsc = put_line "sort" in
  List.fold_left
    (fun (i, defs, basesc) (def: Definition.t) ->
      eprintf "%d:\t%s\n%!" i def.name;
      let memo = Memo.create basesc in
      let defsc =
        match def.proof with
        | None ->
            let _, propsc = put_script memo defs def.context def.prop in
            put_line @@ sprintf "defpr %d %d %s" basesc propsc def.name
        | Some proof ->
            let sc = put_script_with_prop memo defs def.context proof def.prop in
            put_line @@ sprintf "def %d %d %s" basesc sc def.name
      in
      (i + 1, Defs.add def defs, defsc)
    )
    (1, Defs.empty, sortsc) deflist
  |> ignore;
  fprintf !cha "-1\n"
;;
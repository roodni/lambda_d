open Printf
open Syntax

let alpha_equal l r =
  l == r ||
  let lookup env v =
    match List.assoc_opt v env with
    | None -> Error v
    | Some x -> Ok x
  in
  let rec alpha_equal n l_env r_env l r =
    let aeq = alpha_equal n l_env r_env in
    match l, r with
    | Term.Star, Term.Star | Square, Square -> true
    | Var l, Var r -> lookup l_env l = lookup r_env r
    | (App (l1, l2) | AppNF (l1, l2)),
      (App (r1, r2) | AppNF (r1, r2)) ->
        aeq l1 r1 && aeq l2 r2
    | (Lambda (l_x, l_ty, l_bo) | LambdaNF (l_x, l_ty, l_bo)),
      (Lambda (r_x, r_ty, r_bo) | LambdaNF (r_x, r_ty, r_bo))
    | (Pai (l_x, l_ty, l_bo) | PaiNF (l_x, l_ty, l_bo)),
      (Pai (r_x, r_ty, r_bo) | PaiNF (r_x, r_ty, r_bo)) ->
        aeq l_ty r_ty &&
          alpha_equal (n + 1) ((l_x, n) :: l_env) ((r_x, n) :: r_env) l_bo r_bo
    | (Const (l_cv, l_tl) | ConstNF (l_cv, l_tl)),
      (Const (r_cv, r_tl) | ConstNF (r_cv, r_tl)) ->
        l_cv = r_cv &&
          (try List.for_all2 aeq l_tl r_tl with
            Invalid_argument _ -> false)
    | _ -> false
  in
  alpha_equal 0 [] [] l r


let assign_tbl = Hashtbl.create 200
let assign env term =
  let keepnf =
    List.for_all
      (fun (_, term) -> match term with
        | Term.Star | Square | Var _
        | AppNF _ | PaiNF _ | ConstNF _ -> true
        | App _ | Pai _ | Const _
        | Lambda _ | LambdaNF _ -> false )
      env
  in
  let tbl = assign_tbl in
  Hashtbl.clear tbl;
  List.iter
    (fun (x, t) -> Hashtbl.add tbl x t)
    env;
  let rec assign_nf term =
    (* ラムダ項でない正規形だけを代入する場合: 正規形フラグを維持する *)
    match term with
    | Term.Star | Square -> term
    | Var v ->
        ( try Hashtbl.find tbl v
          with Not_found -> term )
    | App (t1, t2) -> App (assign_nf t1, assign_nf t2)
    | AppNF (t1, t2) -> AppNF (assign_nf t1, assign_nf t2)
    | Lambda (x, ty, bo) | LambdaNF (x, ty, bo)
    | Pai (x, ty, bo) | PaiNF (x, ty, bo) -> begin
        let ty' = assign_nf ty in
        let z = Var.gen x in
        Hashtbl.add tbl x (Term.Var z);
        let bo' = assign_nf bo in
        Hashtbl.remove tbl x;
        match term with
        | Lambda _ -> Lambda (z, ty', bo')
        | LambdaNF _ -> LambdaNF (z, ty', bo')
        | Pai _ -> Pai (z, ty', bo')
        | PaiNF _ -> PaiNF (z, ty', bo')
        | _ -> assert false
      end
    | Const (cv, tl) -> Const (cv, List.map assign_nf tl)
    | ConstNF (cv, tl) -> ConstNF (cv, List.map assign_nf tl)
  in
  let rec assign term =
    match term with
    | Term.Star | Square -> term
    | Var v ->
        ( try Hashtbl.find tbl v
          with Not_found -> term )
    | App (t1, t2) | AppNF (t1, t2) ->
        App (assign t1, assign t2)
    | Lambda (x, ty, bo) | LambdaNF (x, ty, bo)
    | Pai (x, ty, bo) | PaiNF (x, ty, bo) -> begin
        let ty' = assign ty in
        let z = Var.gen x in
        Hashtbl.add tbl x (Term.Var z);
        let bo' = assign bo in
        Hashtbl.remove tbl x;
        match term with
        | Lambda _ | LambdaNF _ -> Lambda (z, ty', bo')
        | Pai _ | PaiNF _ -> Pai (z, ty', bo')
        | _ -> assert false
      end
    | Const (cv, tl) | ConstNF (cv, tl) ->
        Const (cv, List.map assign tl)
  in
  if keepnf then assign_nf term
  else assign term

module Context = struct
  type t = (Var.t * Term.t) list

  let equal (l: t) (r: t) =
    l == r ||
    try List.for_all2
      (fun (lv, lt) (rv, rt) ->
        lv = rv && alpha_equal lt rt)
      l r
    with Invalid_argument _ -> false

  let print = function
    | [] -> printf "0"
    | hd :: tl ->
        let print_elm (v, t) =
          printf "%s:" (Var.to_string v);
          Term.print t
        in
        List.iter
          (fun elm -> print_elm elm; printf ", ";)
          (List.rev tl);
        print_elm hd;
end

module Definition = struct
  type t = {
    context: Context.t;
    name: string;
    proof: Term.t option;
    prop: Term.t;
    mutable proofnf: Term.t option;
  }
  let equal l r =
    l == r ||
    ( Context.equal l.context r.context &&
      l.name = r.name &&
      Option.equal alpha_equal l.proof r.proof &&
      alpha_equal l.prop r.prop )

  let print_name def =
    printf "%s[%s]"
      def.name
      (String.concat ","
        (List.map (fun (x, _) -> Var.to_string x) (List.rev def.context)))
  ;;

  let print def =
    Context.print def.context;
    printf " |> ";
    print_name def;
    printf " := ";
    Term.print_proof def.proof;
    printf " : ";
    Term.print def.prop;
  ;;
end

module SMap = Map.Make(String)

module Defs = struct
  type t = int * (int * Definition.t) SMap.t

  let empty : t = (0, SMap.empty)

  let add (def: Definition.t) (n, m: t) : t =
    let m' = SMap.add def.name (n, def) m in
    (n + 1, m')

  let lookupi name (_, m: t) =
    SMap.find_opt name m

  let lookup name defs =
    lookupi name defs |> Option.map snd

  let nth n (_, m: t) =
    SMap.to_seq m
    |> Seq.find_map
      (fun (_, (i, def)) ->
        if i = n then Some def else None)
  let last defs =
    let n, _ = defs in
    nth (n - 1) defs |> Option.get

  let equal (ln, lm: t) (rn, rm: t) =
    lm == rm ||
    ( ln = rn &&
      Seq.for_all2
        (fun (_, (li, ld)) (_, (ri, rd)) ->
           li = ri && Definition.equal ld rd)
        (SMap.to_seq lm)
        (SMap.to_seq rm) )

  let print (_, m: t) =
    let print_def (def: Definition.t) =
      printf "%s" def.name
    in
    let l =
      SMap.to_seq m
      |> List.of_seq
      |> List.sort (fun (_, (li, _)) (_, (ri, _)) -> Int.compare li ri)
    in
    match l with
    | [] -> printf "0"
    | (_, (_, hd)) :: tl ->
        print_def hd;
        List.iter
          (fun (_, (_, def)) -> printf ", "; print_def def;)
          tl
  ;;

  let reportnf (n, m: t) =
    let memon =
      SMap.to_seq m
      |> Seq.filter (fun (_, (_, def)) -> Option.is_some Definition.(def.proofnf))
      |> Seq.length
    in
    eprintf "%d/%d\n" memon n;

end

let rec normal_form defs term =
  match term with
  | Term.Star | Square | Var _
  | AppNF ( _, _) | LambdaNF (_, _, _)
  | PaiNF (_, _, _) | ConstNF (_, _)
      -> term
  | App (t1, t2) -> (
      match normal_form defs t1 with
      | Lambda (x, _, bo) | LambdaNF (x, _, bo) ->
          let t2 = normal_form defs t2 in
          normal_form defs (assign [(x, t2)] bo)
      | t1 -> AppNF (t1, normal_form defs t2)
    )
  | Lambda (x, ty, bo) ->
      LambdaNF (x, normal_form defs ty, normal_form defs bo)
  | Pai (x, ty, bo) ->
      PaiNF (x, normal_form defs ty, normal_form defs bo)
  | Const (name, tl) -> (
      let def = Defs.lookup name defs in
      match def with
      | None -> failwith (sprintf "definition '%s' not found" name)
      | Some ({ proof=Some proof; _ } as def) ->
          let proofnf =
            (* proof *)
            match def.proofnf with
            | Some nf -> nf
            | None ->
                let nf = normal_form defs proof in
                def.proofnf <- Some nf;
                nf
          in
          let ass =
            try
              List.map2
                (fun (x, _) t -> (x, normal_form defs t))
                def.context
                (List.rev tl)
            with Invalid_argument _ -> failwith (sprintf "definition '%s': arity mismatch" name)
          in
          normal_form defs (assign ass proofnf)
      | Some { proof=None; _ } -> ConstNF (name, List.map (normal_form defs) tl)
    )
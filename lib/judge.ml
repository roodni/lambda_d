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


let assign env term =
  let env = env |> List.to_seq |> VMap.of_seq in
  let rec assign env term =
    match term with
    | Term.Star -> Term.Star
    | Square -> Square
    | Var v ->
        ( try VMap.find v env
          with Not_found -> term )
    | App (t1, t2) | AppNF (t1, t2) ->
        App (assign env t1, assign env t2)
    | Lambda (x, ty, bo) | LambdaNF (x, ty, bo)
    | Pai (x, ty, bo) | PaiNF (x, ty, bo) -> begin
        let ty' = assign env ty in
        let env' = VMap.remove x env in
        if VMap.is_empty env' then
          match term with
          | Lambda _ | LambdaNF _ -> Lambda (x, ty', bo)
          | Pai _ | PaiNF _ -> Pai (x, ty', bo)
          | _ -> assert false
        else
          let z = Var.gen x in
          let bo' = assign (VMap.add x (Term.Var z) env') bo in
          match term with
          | Lambda _ | LambdaNF _ -> Lambda (z, ty', bo')
          | Pai _ | PaiNF _ -> Pai (z, ty', bo')
          | _ -> assert false
      end
    | Const (cv, tl) | ConstNF (cv, tl) ->
        Const (cv, List.map (assign env) tl)
  in
  assign env term

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

module Judgement = struct
  type t = {
    definitions: Defs.t;
    context: Context.t;
    proof: Term.t;
    prop: Term.t;
  }

  let print judge =
    (* Defs.print judge.definitions;
    printf "; ";
    Context.print judge.context; *)
    printf "...";
    printf " |- ";
    Term.print judge.proof;
    printf " : ";
    Term.print judge.prop;
  ;;

  let make_sort () =
    { definitions = Defs.empty;
      context = [];
      proof = Star;
      prop = Square;
    }

  let make_var pre var =
    match pre with
    | { definitions;
        context;
        proof;
        prop = Star | Square
      }
      when List.assoc_opt var pre.context |> Option.is_none
      -> Some {
          definitions;
          context = (var, proof) :: context;
          proof = Var var;
          prop = proof;
        }
    | _ -> None

  let make_weak pre1 pre2 var =
    match pre1, pre2 with
    | { definitions=def1; context=ctx1; proof=a; prop=b; },
      { definitions=def2; context=ctx2; proof=c; prop=Star | Square; }
      when
        Defs.equal def1 def2 &&
        Context.equal ctx1 ctx2
      -> Some {
          definitions = def1;
          context = (var, c) :: ctx1;
          proof = a;
          prop = b;
        }
    | _ -> None

  let make_form pre1 pre2 =
    match pre1, pre2 with
    | { definitions=def1; context=ctx1; proof=a1; prop=Star | Square; },
      { definitions=def2; context=(x, a2) :: ctx2; proof=b; prop=Star | Square as s }
      when
        Defs.equal def1 def2 &&
        Context.equal ctx1 ctx2 &&
        alpha_equal a1 a2
      -> Some {
          definitions = def1;
          context = ctx1;
          proof = Pai (x, a1, b);
          prop = s
        }
    | _ -> None

  let make_appl pre1 pre2 =
    match pre1, pre2 with
    | { definitions=def1; context=ctx1; proof=m; prop=Pai (x, a1, b); },
      { definitions=def2; context=ctx2; proof=n; prop=a2; }
      when
        Defs.equal def1 def2 &&
        Context.equal ctx1 ctx2 &&
        alpha_equal a1 a2
      -> Some {
          definitions = def1;
          context = ctx1;
          proof = App (m, n);
          prop = assign [(x, n)] b;
        }
    | _ -> None

  let make_abst pre1 pre2 =
    match pre1, pre2 with
    | { definitions=def1; context=(x1, a1) :: ctx1; proof=m; prop=b1; },
      { definitions=def2; context=ctx2; proof=Pai (x2, a2, b2); prop=Star | Square }
      when
        Defs.equal def1 def2 &&
        Context.equal ctx1 ctx2 &&
        x1 = x2 &&
        alpha_equal a1 a2 &&
        alpha_equal b1 b2
      -> Some {
          definitions = def1;
          context = ctx1;
          proof = Lambda (x1, a1, m);
          prop = Pai (x1, a1, b1)
        }
    | _ -> None

  let make_conv pre1 pre2 =
    match pre1, pre2 with
    | { definitions=def1; context=ctx1; proof=a; prop=b; },
      { definitions=def2; context=ctx2; proof=b'; prop=Star | Square; }
      when
        Defs.equal def1 def2 &&
        Context.equal ctx1 ctx2;
      ->
        let nf1 = normal_form def1 b in
        let nf2 = normal_form def2 b' in
        (* printf "  nf1: "; Term.print nf1; printf "\n";
        printf "  nf2: "; Term.print nf2; printf "\n"; *)
        if alpha_equal nf1 nf2 then
          Some {
            definitions = def1;
            context = ctx1;
            proof = a;
            prop = b';
          }
        else None
    | _ -> None

  let make_def pre1 pre2 name =
    match pre1, pre2 with
    | { definitions=def1; context; proof=k; prop=l; },
      { definitions=def2; context=ctx_def; proof=m; prop=n; }
      when Defs.equal def1 def2 ->
        Some {
          definitions =
            Defs.add
              { context=ctx_def; name; proof=Some m; prop=n; proofnf=None; }
              def1;
          context;
          proof = k;
          prop = l;
        }
    | _ -> None

  let make_def_prim  pre1 pre2 name =
    match pre1, pre2 with
    | { definitions=def1; context; proof=k; prop=l; },
      { definitions=def2; context=ctx_def; proof=n; prop=Star | Square; }
      when Defs.equal def1 def2 ->
        Some {
          definitions =
            Defs.add
              { context=ctx_def; name; proof=None; prop=n; proofnf=None; }
              def1;
          context;
          proof = k;
          prop = l;
        }
    | _ -> None

  let make_inst ~prim pre1 pres p =
    match
      let defs, ctx =
        match pre1 with
        | { definitions; context; proof=Star; prop=Square } -> (definitions, context)
        | _ -> raise Exit
      in
      let def =
        match Defs.nth p defs with
        | Some def -> def
        | None -> raise Exit
      in
      (* printf "  def:"; Definition.print def; printf "\n"; *)
      if prim && Option.is_some def.proof then raise Exit;
      (* if not prim && Option.is_none def.proof then raise Exit; *)
      let ctx_and_pres =
        (* 定義のコンテキストの各バインディング と 前提の判断 の組のリスト *)
        try List.map2 (fun b p -> (b, p)) def.context (List.rev pres)
        with Invalid_argument _ -> raise Exit (* ここで pres と def.context の要素数が等しいことがわかる *)
      in
      let ass =
        List.map (fun ((x, _), p) -> (x, p.proof)) ctx_and_pres
      in
      (* printf "  pre1:"; print pre1; printf "\n"; *)
      List.iter
        (fun ((_, a), p) ->
          let cond =
            Defs.equal defs p.definitions &&
            Context.equal ctx p.context &&
            alpha_equal p.prop (assign ass a)
          in
          (* printf "  prei:"; print p; printf "\n";
          printf "         "; Term.print p.prop; printf "\n";
          printf "         "; Term.print (assign ass a); printf "\n"; *)
          (* assert (Definition.equal_all defs p.definitions);
          assert (Context.equal ctx p.context);
          assert (alpha_equal p.prop (assign ass a)); *)
          if not cond then raise Exit)
        ctx_and_pres;
      { definitions = defs;
        context = ctx;
        proof = Const (def.name, List.map (fun p -> p.proof) pres);
        prop = assign ass def.prop;
      }
    with
    | j -> Some j
    | exception Exit -> None
end
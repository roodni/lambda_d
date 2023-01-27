open Printf

open Syntax
open Conv

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
        proof = Term.pai x a1 b;
        prop = s
      }
  | _ -> None

let make_appl pre1 pre2 =
  match pre1, pre2 with
  | { definitions=def1; context=ctx1; proof=m; prop=Pai (x, a1, b, _); },
    { definitions=def2; context=ctx2; proof=n; prop=a2; }
    when
      Defs.equal def1 def2 &&
      Context.equal ctx1 ctx2 &&
      alpha_equal a1 a2
    -> Some {
        definitions = def1;
        context = ctx1;
        proof = Term.app m n;
        prop = assign [(x, n)] b;
      }
  | _ -> None

let make_abst pre1 pre2 =
  match pre1, pre2 with
  | { definitions=def1; context=(x1, a1) :: ctx1; proof=m; prop=b1; },
    { definitions=def2; context=ctx2; proof=Pai (x2, a2, b2, _); prop=Star | Square }
    when
      let b2 =
        if x1 = x2 then b2 else assign [(x2, Var x1)] b2
      in
      Defs.equal def1 def2 &&
      Context.equal ctx1 ctx2 &&
      (* x1 = x2 && *)
      alpha_equal a1 a2 &&
      alpha_equal b1 b2
    -> Some {
        definitions = def1;
        context = ctx1;
        proof = Term.lambda x1 a1 m;
        prop = Term.pai x1 a1 b1
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
      (* eprintf "nf1 %!"; *)
      let nf1 = normal_form def1 b in
      (* eprintf "nf2 %!"; *)
      let nf2 = normal_form def2 b' in
      (* eprintf "alpha %!"; *)
      (* printf "  nf1: "; Term.print nf1; printf "\n";
      printf "  nf2: "; Term.print nf2; printf "\n"; *)
      if alpha_equal nf1 nf2 then
        (* let () = eprintf "done\n%!" in *)
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
      proof = Term.const def.name (List.map (fun p -> p.proof) pres);
      prop = assign ass def.prop;
    }
  with
  | j -> Some j
  | exception Exit -> None

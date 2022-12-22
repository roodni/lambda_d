open Printf

open Syntax
open Term

let alpha_equal l r =
  let lookup env v =
    match List.assoc_opt v env with
    | None -> Error v
    | Some x -> Ok x
  in
  let rec alpha_equal n l_env r_env l r =
    let aeq = alpha_equal n l_env r_env in
    match l, r with
    | Star, Star | Sort, Sort -> true
    | Var l, Var r -> lookup l_env l = lookup r_env r
    | App (l1, l2), App (r1, r2) -> aeq l1 r1 && aeq l2 r2
    | Lambda (l_x, l_ty, l_bo), Lambda (r_x, r_ty, r_bo) |
      Pai (l_x, l_ty, l_bo), Pai (r_x, r_ty, r_bo) ->
        aeq l_ty r_ty &&
          alpha_equal (n + 1) ((l_x, n) :: l_env) ((r_x, n) :: r_env) l_bo r_bo
    | Const (l_cv, l_tl), Const (r_cv, r_tl) ->
        l_cv = r_cv &&
          (try List.for_all2 aeq l_tl r_tl with
            Invalid_argument _ -> false)
    | _ -> false
  in
  alpha_equal 0 [] [] l r


let rec assign env term =
  let ass = assign env in
  match term with
  | Star -> Star
  | Sort -> Sort
  | Var v -> (
      match List.assoc_opt v env with
      | None -> Var v
      | Some t -> t
    )
  | App (t1, t2) -> App (ass t1, ass t2)
  | Lambda (x, ty, bo) | Pai (x, ty, bo) -> (
      let z = Var.gen x in
      let ty' = ass ty in
      let bo' = ass (assign [(x, Var z)] bo) in
      match term with
      | Lambda _ -> Lambda (z, ty', bo')
      | Pai _ -> Pai (z, ty', bo')
      | _ -> assert false
    )
  | Const (cv, tl) -> Const (cv, List.map ass tl)

let beta_reduction term =
  assert false

module Definition = struct
  type t = unit
  let equal l r = l = r
  let equal_all (l: t list) (r: t list) =
    try List.for_all2 (fun l r -> equal l r) l r with
    | Invalid_argument _ -> false
  let print_all _def = printf "0"
end

module Context = struct
  type t = (Var.t * Term.t) list

  let equal (l: t) (r: t) =
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

module Judgement = struct
  type t = {
    definitions: Definition.t list;
    context: Context.t;
    proof: Term.t;
    prop: Term.t;
  }

  let print judge =
    Definition.print_all judge.definitions;
    printf " ; ";
    Context.print judge.context;
    printf " |- ";
    Term.print judge.proof;
    printf " : ";
    Term.print judge.prop;
  ;;

  let make_sort () =
    { definitions = [];
      context = [];
      proof = Star;
      prop = Sort;
    }

  let make_var pre var =
    match pre with
    | { definitions;
        context;
        proof;
        prop = Star | Sort
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
      { definitions=def2; context=ctx2; proof=c; prop=Star | Sort; }
      when
        Definition.equal_all def1 def2 &&
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
    | { definitions=def1; context=ctx1; proof=a1; prop=Star | Sort; },
      { definitions=def2; context=(x, a2) :: ctx2; proof=b; prop=Star | Sort as s }
      when
        Definition.equal_all def1 def2 &&
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
        Definition.equal_all def1 def2 &&
        Context.equal ctx1 ctx2 &&
        alpha_equal a1 a2
      -> Some {
          definitions = def1;
          context = ctx1;
          proof = App (m, n);
          prop = assign [(x, n)] b;
        }
    | _ -> None
end
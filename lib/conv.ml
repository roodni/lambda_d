open Printf
open Syntax

let l_env = Hashtbl.create 1000
let r_env = Hashtbl.create 1000
let alpha_equal l r =
  let lookup env v =
    try Hashtbl.find env v
    with Not_found -> v
  in
  Hashtbl.clear l_env;
  Hashtbl.clear r_env;
  let rec eq n l r =
    l == r ||
    match l, r with
    | Term.Star, Term.Star | Square, Square -> true
    | Var l, Var r -> lookup l_env l = lookup r_env r
    | (App (l1, l2, _) | AppNF (l1, l2, _)),
      (App (r1, r2, _) | AppNF (r1, r2, _)) ->
        eq n l1 r1 && eq n l2 r2
    | (Lambda (l_x, l_ty, l_bo, _) | LambdaNF (l_x, l_ty, l_bo, _)),
      (Lambda (r_x, r_ty, r_bo, _) | LambdaNF (r_x, r_ty, r_bo, _))
    | (Pai (l_x, l_ty, l_bo, _) | PaiNF (l_x, l_ty, l_bo, _)),
      (Pai (r_x, r_ty, r_bo, _) | PaiNF (r_x, r_ty, r_bo, _)) ->
        eq n l_ty r_ty &&
          (
            if l_x = r_x &&
                not (Hashtbl.mem l_env l_x || Hashtbl.mem r_env r_x)
              then eq n l_bo r_bo
              else begin
                Hashtbl.add l_env l_x n;
                Hashtbl.add r_env r_x n;
                let res = eq (n - 1) l_bo r_bo in
                Hashtbl.remove l_env l_x;
                Hashtbl.remove r_env r_x;
                res
              end
          )
    | (Const (l_cv, l_tl, _) | ConstNF (l_cv, l_tl, _)),
      (Const (r_cv, r_tl, _) | ConstNF (r_cv, r_tl, _)) ->
        l_cv = r_cv &&
          (try List.for_all2 (eq n) l_tl r_tl with
            Invalid_argument _ -> false)
    | _ -> false
  in
  eq (-1) l r


let assign_tbl = Hashtbl.create 200
let assign env term =
  let keepnf = function
    | Term.Star | Square | Var _
    | AppNF _ | PaiNF _ | ConstNF _ -> true
    | App _ | Pai _ | Const _
    | Lambda _ | LambdaNF _ -> false
  in
  let tbl = assign_tbl in
  Hashtbl.clear tbl;
  List.iter
    (fun (x, t) -> Hashtbl.add tbl x t)
    env;
  let rec assign term =
    (* let check_free _ = (true, false) in *)
    let check_free fvset =
      let found = ref false in
      let nf = ref true in
      VSet.iter
        (fun fv ->
          match Hashtbl.find tbl fv with
          | t ->
              found := true;
              if !nf then nf := keepnf t;
          | exception Not_found -> () )
        fvset;
      (!found, !nf)
    in
    match term with
    | Term.Star | Square -> term
    | Var v ->
        ( try Hashtbl.find tbl v
          with Not_found -> term )
    | App (t1, t2, free) | AppNF (t1, t2, free) ->
        let found, nf = check_free free in
        if found then
          let nf = match term with
            | AppNF _ -> nf
            | _ -> false
          in
          Term.app ~nf (assign t1) (assign t2)
        else term
    | Lambda (x, ty, bo, free) | LambdaNF (x, ty, bo, free)
    | Pai (x, ty, bo, free) | PaiNF (x, ty, bo, free) -> begin
        let found = ref false in
        let nf = ref true in
        let xdup = ref false in
        VSet.iter
          (fun fv ->
            match Hashtbl.find tbl fv with
            | t ->
                found := true;
                if !nf then nf := keepnf t;
                if not !xdup && VSet.mem x (Term.free t)
                  then xdup := true;
            | exception Not_found -> () )
          free;
        let nf = !nf in
        if not !found then term
        else
          let ty' = assign ty in
          let xt = Hashtbl.find_opt tbl x in
          Hashtbl.remove tbl x;
          let z =
            if !xdup then
              let z = Var.gen x in
              Hashtbl.add tbl x (Term.Var z);
              z
            else x
          in
          let bo' = assign bo in
          ( match xt with
            | Some xt -> Hashtbl.replace tbl x xt
            | None -> if !xdup then Hashtbl.remove tbl x
          );
          match term with
          | Lambda _ -> Term.lambda z ty' bo'
          | LambdaNF _ -> Term.lambda ~nf z ty' bo'
          | Pai _ -> Term.pai z ty' bo'
          | PaiNF _ -> Term.pai ~nf z ty' bo'
          | _ -> assert false
      end
    | Const (cv, tl, free) | ConstNF (cv, tl, free) ->
        let found, nf = check_free free in
        if found then
          let nf = match term with
            | ConstNF _ -> nf
            | _ -> false
          in
          Term.const ~nf cv (List.map assign tl)
        else term
  in
  assign term

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
  | AppNF _ | LambdaNF _
  | PaiNF _ | ConstNF _
      -> term
  | App (t1, t2, _) -> (
      match normal_form defs t1 with
      | Lambda (x, _, bo, _) | LambdaNF (x, _, bo, _) ->
          let t2 = normal_form defs t2 in
          normal_form defs (assign [(x, t2)] bo)
      | t1 -> Term.app ~nf:true t1 (normal_form defs t2)
    )
  | Lambda (x, ty, bo, _) ->
      Term.lambda ~nf:true x (normal_form defs ty) (normal_form defs bo)
  | Pai (x, ty, bo, _) ->
      Term.pai ~nf:true x (normal_form defs ty) (normal_form defs bo)
  | Const (name, tl, _) -> (
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
      | Some { proof=None; _ } -> Term.const ~nf:true name (List.map (normal_form defs) tl)
    )

let rec outermost_reduction defs term =
  match term with
  | Term.Star | Square | Var _
  | Lambda _ | LambdaNF _
  | Pai _ | PaiNF _ ->
      term
  | App (l, r, _) | AppNF (l, r, _) -> begin
      match outermost_reduction defs l with
      | Lambda (x, _, bo, _) | LambdaNF (x, _, bo, _) ->
          assign [(x, r)] bo
          |> outermost_reduction defs
      | _ -> term
    end
  | Const (name, tl, _) | ConstNF (name, tl, _) -> begin
      let def = Defs.lookup name defs in
      match def with
      | None -> failwith (sprintf "definition '%s' not found" name)
      | Some { proof=None; _ } -> term
      | Some ({ proof=Some proof; _ } as def) ->
          let ass =
            try
              List.map2
                (fun (x, _) t -> (x, t))
                def.context
                (List.rev tl)
            with Invalid_argument _ -> failwith (sprintf "definition '%s': arity mismatch" name)
          in
          assign ass proof
          |> outermost_reduction defs
    end
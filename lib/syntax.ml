open Printf

module Var = struct
  type t = int

  let name_to_id: (string, t) Hashtbl.t = Hashtbl.create 100
  let id_to_name: (t, string) Hashtbl.t = Hashtbl.create 100

  let vari = ref 0

  let named s =
    match Hashtbl.find_opt name_to_id s with
    | Some i -> i
    | None ->
        let v = !vari in
        incr vari;
        Hashtbl.add name_to_id s v;
        Hashtbl.add id_to_name v s;
        v
  let gen _v =
    let v' = !vari in
    incr vari;
    v'

  let to_string v =
    match Hashtbl.find_opt id_to_name v with
    | Some s -> s
    | _ -> sprintf "_%d" v

  let compare = Int.compare
end

module VSet = Set.Make(Var)

module Term = struct
  type t =
    | Star
    | Square
    | Var of Var.t
    | App of t * t * VSet.t
    | AppNF of t * t * VSet.t
    | Lambda of Var.t * t * t * VSet.t
    | LambdaNF of Var.t * t * t * VSet.t
    | Pai of Var.t * t * t * VSet.t
    | PaiNF of Var.t * t * t * VSet.t
    | Const of string * t list * VSet.t
    | ConstNF of string * t list * VSet.t

  let free = function
    | Star | Square -> VSet.empty
    | Var x -> VSet.singleton x
    | App (_, _, s) | Const (_, _, s)
    | Lambda (_, _, _, s) | Pai (_, _, _, s)
    | AppNF (_, _, s) | ConstNF (_, _, s)
    | LambdaNF (_, _, _, s) | PaiNF (_, _, _, s) -> s
  let mem_free v = function
    | Star | Square -> false
    | Var x -> v = x
    | t -> VSet.mem v (free t)
  let add_free t set =
    match t with
    | Star | Square -> set
    | Var x -> VSet.add x set
    | _ -> VSet.union (free t) set

  let app ?(nf=false) l r =
    let s = free l |> add_free r in
    if nf then AppNF (l, r, s)
      else App (l, r, s)
  let lambda ?(nf=false) v ty bo =
    let s = free bo |> VSet.remove v |> add_free ty in
    if nf then LambdaNF (v, ty, bo, s)
      else Lambda (v, ty, bo, s)
  let pai ?(nf=false) v ty bo =
    let s = free bo |> VSet.remove v |> add_free ty in
    if nf then PaiNF (v, ty, bo, s)
      else Pai (v, ty, bo, s)
  let const ?(nf=false) name tl =
    let s = match tl with
      | [] -> VSet.empty
      | [t] -> free t
      | h :: rest ->
          List.fold_left (fun s t -> add_free t s) (free h) rest
    in
    if nf then ConstNF (name, tl, s)
      else Const (name, tl, s)

  let to_buf term =
    let buf = Buffer.create 100 in
    let pf fmt = bprintf buf fmt in
    let rec print_term = function
      | Star -> pf "*"
      | Square -> pf "@"
      | Var v -> pf "%s" (Var.to_string v)
      | App (t1, t2, _) | AppNF(t1, t2, _) ->
          pf "%%("; print_term t1; pf ")("; print_term t2; pf ")"
      | Lambda (v, ty, body, _) | LambdaNF (v, ty, body, _) ->
          pf "$%s:(" (Var.to_string v);
          print_term ty;
          pf ").(";
          print_term body;
          pf ")"
      | Pai (v, ty, body, _) | PaiNF(v, ty, body, _) ->
          pf "?%s:(" (Var.to_string v);
          print_term ty;
          pf ").(";
          print_term body;
          pf ")"
      | Const (name, terms, _) | ConstNF (name, terms, _) ->
          pf "%s[" name;
          List.iteri
            (fun i t ->
              if i > 0 then pf ",";
              pf "("; print_term t; pf ")"
            )
            terms;
          pf "]"
    in
    print_term term;
    buf

  let to_string term =
    to_buf term |> Buffer.contents

  let output channel term =
    Buffer.output_buffer channel (to_buf term)
  let print term = output stdout term

  let print_proof = function
    | None -> print_string "#"
    | Some t -> print t
end

type figure_elm =
  | Definition of [`Global | `Local] * string * (Var.t list) option * Term.t option * Term.t
  | Context of (Var.t * Term.t) list * figure_elm list

type figure = string * figure_elm list
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

module VMap = Map.Make(Var)

module Term = struct
  type t =
    | Star
    | Square
    | Var of Var.t
    | App of t * t
    | AppNF of t * t
    | Lambda of Var.t * t * t
    | LambdaNF of Var.t * t * t
    | Pai of Var.t * t * t
    | PaiNF of Var.t * t * t
    | Const of string * t list
    | ConstNF of string * t list

  let rec delete_nf term =
    match term with
    | Star | Square | Var _ -> term
    | App (t1, t2) | AppNF (t1, t2) ->
        App (delete_nf t1, delete_nf t2)
    | Lambda (x, t1, t2) | LambdaNF (x, t1, t2) ->
        Lambda (x, delete_nf t1, delete_nf t2)
    | Pai (x, t1, t2) | PaiNF (x, t1, t2) ->
        Pai (x, delete_nf t1, delete_nf t2)
    | Const (name, tl) | ConstNF (name, tl) ->
        Const (name, List.map delete_nf tl)

  let to_buf term =
    let buf = Buffer.create 100 in
    let pf fmt = bprintf buf fmt in
    let rec print_term = function
      | Star -> pf "*"
      | Square -> pf "@"
      | Var v -> pf "%s" (Var.to_string v)
      | App (t1, t2) | AppNF(t1, t2) ->
          pf "%%("; print_term t1; pf ")("; print_term t2; pf ")"
      | Lambda (v, ty, body) | LambdaNF (v, ty, body) ->
          pf "$%s:(" (Var.to_string v);
          print_term ty;
          pf ").(";
          print_term body;
          pf ")"
      | Pai (v, ty, body) | PaiNF(v, ty, body) ->
          pf "?%s:(" (Var.to_string v);
          print_term ty;
          pf ").(";
          print_term body;
          pf ")"
      | Const (name, terms) | ConstNF (name, terms) ->
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
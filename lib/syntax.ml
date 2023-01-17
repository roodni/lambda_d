open Printf

module Var = struct
  type t = Named of string | Generated of string * int

  let to_string = function
    | Named n -> n
    (* | Generated (n, i) -> sprintf "%d%s" i n *)
    | Generated (n, i) -> sprintf "%s%d" n i

  let vari = ref 0
  let gen v =
    let Named n | Generated (n, _) = v in
    incr vari;
    Generated (n, !vari)

  let compare (l: t) (r: t) =
    let geti = function
      | Named _ -> -1
      | Generated (_, i) -> i
    in
    let getn = function
      | Named n -> n
      | Generated (n, _) -> n
    in
    let li = geti l in
    let ri = geti r in
    let res = Int.compare li ri in
    if res <> 0 || li <> -1 then res
    else String.compare (getn l) (getn r)

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
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
  type nf = NF | MaybeNF

  type t =
    | Star
    | Square
    | Var of Var.t
    | App of nf * t * t
    | Lambda of nf * Var.t * t * t
    | Pai of nf * Var.t * t * t
    | Const of nf * string * t list

  let to_buf term =
    let buf = Buffer.create 100 in
    let pf fmt = bprintf buf fmt in
    let rec print_term = function
      | Star -> pf "*"
      | Square -> pf "@"
      | Var v -> pf "%s" (Var.to_string v)
      | App (_, t1, t2) ->
          pf "%%("; print_term t1; pf ")("; print_term t2; pf ")"
      | Lambda (_, v, ty, body) ->
          pf "$%s:(" (Var.to_string v);
          print_term ty;
          pf ").(";
          print_term body;
          pf ")"
      | Pai (_, v, ty, body) ->
          pf "?%s:(" (Var.to_string v);
          print_term ty;
          pf ").(";
          print_term body;
          pf ")"
      | Const (_, name, terms) ->
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
open Printf

module Var = struct
  type t = Named of string | Generated of string * int

  let to_string = function
    | Named n -> n
    | Generated (n, i) -> sprintf "%d%s" i n

  let vari = ref 0
  let gen v =
    let Named n | Generated (n, _) = v in
    incr vari;
    Generated (n, !vari)
end

module Term = struct
  type t =
    | Star
    | Sort
    | Var of Var.t
    | App of t * t
    | Lambda of Var.t * t * t
    | Pai of Var.t * t * t
    | Const of string * t list

  let to_buf term =
    let buf = Buffer.create 100 in
    let pf fmt = bprintf buf fmt in
    let rec print_term = function
      | Star -> pf "*"
      | Sort -> pf "@"
      | Var v -> pf "%s" (Var.to_string v)
      | App (t1, t2) ->
          pf "%%("; print_term t1; pf ")("; print_term t2; pf ")"
      | Lambda (v, ty, body) ->
          pf "$%s:(" (Var.to_string v);
          print_term ty;
          pf ").(";
          print_term body;
          pf ")"
      | Pai (v, ty, body) ->
          pf "?%s:(" (Var.to_string v);
          print_term ty;
          pf ").(";
          print_term body;
          pf ")"
      | Const (name, terms) ->
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
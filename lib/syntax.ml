open Printf

type var = string
type cvar = string

type term =
  | Kind
  | Sort
  | Var of var
  | App of term * term
  | Lambda of var * term * term
  | Pai of var * term * term
  | Const of cvar * term list

(* let rec term_to_string = function
  | Kind -> "*"
  | Sort -> "@"
  | Var s -> s
  | App (t1, t2) -> sprintf "%%(%s)(%s)" (term_to_string t1) (term_to_string t2)
  | Lambda (v, ty, body) -> sprintf "$%s:(%s).(%s)" v (term_to_string ty) (term_to_string body)
  | Pai (v, ty, body) -> sprintf "?%s:(%s).(%s)" v (term_to_string ty) (term_to_string body)
  | Const (name, terms) ->
      sprintf "%s[%s]"
        name
        ( List.map
            (fun t -> sprintf "(%s)" (term_to_string t))
            terms
          |> String.concat ",") *)


let term_to_buf term =
  let buf = Buffer.create 100 in
  let pf fmt = bprintf buf fmt in
  let rec print_term = function
    | Kind -> pf "*"
    | Sort -> pf "@"
    | Var s -> pf "%s" s
    | App (t1, t2) ->
        pf "%%("; print_term t1; pf ")("; print_term t2; pf ")"
    | Lambda (v, ty, body) ->
        pf "$%s:(" v;
        print_term ty;
        pf ").(";
        print_term body;
        pf ")"
    | Pai (v, ty, body) ->
        pf "?%s:(" v;
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

let output_term channel term =
  Buffer.output_buffer channel (term_to_buf term)
let print_term term = output_term stdout term
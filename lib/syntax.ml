open Printf

type var = Named of string | Generated of int

let string_of_var = function
  | Named n -> n
  | Generated i -> sprintf "#%d" i

module Term = struct
  type t =
    | Kind
    | Sort
    | Var of var
    | App of t * t
    | Lambda of var * t * t
    | Pai of var * t * t
    | Const of string * t list

  let vari = ref 0
  let gen_var () =
    incr vari;
    Generated !vari

  let to_buf term =
    let buf = Buffer.create 100 in
    let pf fmt = bprintf buf fmt in
    let rec print_term = function
      | Kind -> pf "*"
      | Sort -> pf "@"
      | Var v -> pf "%s" (string_of_var v)
      | App (t1, t2) ->
          pf "%%("; print_term t1; pf ")("; print_term t2; pf ")"
      | Lambda (v, ty, body) ->
          pf "$%s:(" (string_of_var v);
          print_term ty;
          pf ").(";
          print_term body;
          pf ")"
      | Pai (v, ty, body) ->
          pf "?%s:(" (string_of_var v);
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

end
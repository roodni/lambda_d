open Printf

open Syntax
open Judge

let load_figures lexbuf =
  try Parser.deflang Lexer.main lexbuf with
  | Lexer.Error | Parser.Error ->
      let Lexing.{ pos_lnum; pos_cnum; pos_bol; _ } = Lexing.lexeme_start_p lexbuf in
      failwith
      @@ sprintf "line %d, col %d: parse error"
          pos_lnum
          (1 + pos_cnum - pos_bol)

let rec replace_const f = function
  | Term.Star -> Term.Star
  | Square -> Square
  | Var v -> Var v
  | App (l, r) -> App (replace_const f l, replace_const f r)
  | Lambda (v, ty, bo) -> Lambda (v, replace_const f ty, replace_const f bo)
  | Pai (v, ty, bo) -> Pai (v, replace_const f ty, replace_const f bo)
  | Const (name, l) -> Const (f name, List.map (replace_const f) l)

let figure_to_definitions (figname, elms: figure) =
  let defs = ref [] in
  let nametbl = Hashtbl.create 30 in
  let local_to_global local =
    Hashtbl.find_opt nametbl local
    |> Option.value ~default:local
  in
  let rec convert ctx = function
    | Definition (scope, name, vl_opt, proof, prop) ->
        let global_name = match scope with
          | `Global -> name
          | `Local -> sprintf "%s_%s" figname name
        in
        Hashtbl.add nametbl name global_name;
        let defctx =
          match vl_opt with
          | None -> ctx
          | Some vl ->
            List.rev_map
              (fun v ->
                match List.assoc_opt v ctx with
                | Some t -> (v, t)
                | None ->
                    failwith
                    @@ sprintf "%s: variable '%s' not found"
                        global_name (Var.to_string v) )
              vl
        in
        let def = Definition.{
          context = defctx;
          name = global_name;
          proof = Option.map (replace_const local_to_global) proof;
          prop = replace_const local_to_global prop;
        } in
        defs := def :: !defs;
    | Context (bindings, elms) ->
        let ctx =
          List.rev_map (fun (v, t) -> (v, replace_const local_to_global t)) bindings
          @ ctx
        in
        convert_elms ctx elms;
  and convert_elms ctx elms =
    List.iter (convert ctx) elms
  in
  convert_elms [] elms;
  List.rev !defs
;;

let print_definition def =
  let open Definition in
  let { context; name; proof; prop; } = def in
  print_endline "def2";
  printf "%d\n" (List.length context);
  List.iter
    (fun (v, t) ->
      print_endline (Var.to_string v);
      Term.print t;
      print_newline (); )
    (List.rev context);
  print_endline name;
  Term.print_proof proof;
  print_newline ();
  Term.print prop;
  print_newline ();
  print_endline "edef2"
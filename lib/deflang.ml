open Printf
open Scanf

open Syntax
open Conv

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
  | App (l, r, _) | AppNF (l, r, _) ->
      Term.app (replace_const f l) (replace_const f r)
  | Lambda (v, ty, bo, _) | LambdaNF (v, ty, bo, _) ->
      Term.lambda v (replace_const f ty) (replace_const f bo)
  | Pai (v, ty, bo, _) | PaiNF (v, ty, bo, _) ->
      Term.pai v (replace_const f ty) (replace_const f bo)
  | Const (name, l, _) | ConstNF (name, l, _) ->
      Term.const (f name) (List.map (replace_const f) l)

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
          proofnf = None;
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


let string_to_term s =
  let lexbuf = Lexing.from_string s in
  let term =
    try Parser.main Lexer.main lexbuf with
    | Parser.Error | Lexer.Error -> raise (Invalid_argument s)
  in
  term
;;

(* 定義の授業文法 *)
module Def2 = struct
  let print def =
    let open Definition in
    let { context; name; proof; prop; _ } = def in
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

  let load channel =
    let ib = Scanning.from_channel channel in
    let rec scan_defs defs =
      let s = bscanf ib "%s " (fun s -> s) in
      match s with
      | "END" -> List.rev defs
      | "def2" ->
          let n = bscanf ib "%d " (fun n -> n) in
          let rec scan_ctx n ctx =
            if n = 0 then ctx
            else
              let ctx =
                bscanf ib "%s %s "
                  (fun v t -> (Var.named v, string_to_term t) :: ctx)
              in
              scan_ctx (n - 1) ctx
          in
          let context = scan_ctx n [] in
          let def =
            bscanf ib "%s %s %s %s "
              (fun name proof prop ed ->
                assert (ed = "edef2");
                Definition.{
                  name;
                  context;
                  proof =
                    if proof = "#" then None
                    else Some (string_to_term proof);
                  prop = string_to_term prop;
                  proofnf = None;
                }
              )
          in
          scan_defs (def :: defs)
      | _ -> failwith "'def2' or 'END' expected"
    in
    scan_defs []
end
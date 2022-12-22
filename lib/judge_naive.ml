open Syntax
open Term

let rec assign_var l r term =
  match term with
  | Star -> Star
  | Sort -> Sort
  | Var v when v = l -> Var r
  | Var v -> Var v
  | App (t1, t2) -> App (assign_var l r t1, assign_var l r t2)
  | Lambda (x, ty, bo) | Pai (x, ty, bo) ->
      let x, ty, bo =
        if x = l then (x, assign_var l r ty, bo)
        else if x = r then
          let z = gen_var () in
          (z, assign_var l r ty,
              assign_var l r (assign_var x z bo))
        else (x, assign_var l r ty, assign_var l r bo)
      in
      ( match term with
        | Lambda _ -> Lambda (x, ty, bo)
        | Pai _ -> Pai (x, ty, bo)
        | _ -> assert false )
  | Const (cv, tl) ->
      Const (cv, List.map (assign_var l r) tl)
;;

let rec alpha_equal l r =
  match l, r with
  | Star, Star | Sort, Sort -> true
  | Var v1, Var v2 -> v1 = v2
  | App (l1, l2), App (r1, r2) -> alpha_equal l1 r1 && alpha_equal l2 r2
  | Lambda (l_x, l_ty, l_bo), Lambda (r_x, r_ty, r_bo) |
    Pai (l_x, l_ty, l_bo), Pai (r_x, r_ty, r_bo) ->
      alpha_equal l_ty r_ty &&
        (let z = gen_var () in
          alpha_equal (assign_var l_x z l_bo) (assign_var r_x z r_bo))
  | Const (l_cv, l_tl), Const (r_cv, r_tl) ->
      l_cv = r_cv &&
        (try List.for_all2 alpha_equal l_tl r_tl with
          Invalid_argument _ -> false)
  | _ -> false
;;
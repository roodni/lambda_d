open Syntax
open Term

let rec assign_var l r term =
  match term with
  | Kind -> Kind
  | Sort -> Sort
  | Var v when v = l -> Var r
  | Var v -> Var v
  | App (t1, t2) -> App (assign_var l r t1, assign_var l r t2)
  | Lambda (x, ty, bo) | Pai (x, ty, bo) ->
      let x, ty, bo =
        if x = l then (x, ty, bo)
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
  | Kind, Kind | Sort, Sort -> true
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

let alpha_equal2 l r =
  let lookup env v =
    match List.assoc_opt v env with
    | None -> Error v
    | Some x -> Ok x
  in
  let rec alpha_equal n l_env r_env l r =
    let aeq = alpha_equal n l_env r_env in
    match l, r with
    | Kind, Kind | Sort, Sort -> true
    | Var l, Var r -> lookup l_env l = lookup r_env r
    | App (l1, l2), App (r1, r2) -> aeq l1 r1 && aeq l2 r2
    | Lambda (l_x, l_ty, l_bo), Lambda (r_x, r_ty, r_bo) |
      Pai (l_x, l_ty, l_bo), Pai (r_x, r_ty, r_bo) ->
        aeq l_ty r_ty &&
          alpha_equal (n + 1) ((l_x, n) :: l_env) ((r_x, n) :: r_env) l_bo r_bo
    | Const (l_cv, l_tl), Const (r_cv, r_tl) ->
        l_cv = r_cv &&
          (try List.for_all2 aeq l_tl r_tl with
            Invalid_argument _ -> false)
    | _ -> false
  in
  alpha_equal 0 [] [] l r
type term =
  | Kind
  | Sort

let term_to_string = function
  | Kind -> "kind"
  | Sort -> "sort"
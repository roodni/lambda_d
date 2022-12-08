{
module P = Parser
}

rule main = parse
  | [' ' '\t' '\r' '\n']+ { main lexbuf }
  | "*" { P.ASTER }
  | "@" { P.AT }
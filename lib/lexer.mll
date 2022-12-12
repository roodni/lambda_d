{
module P = Parser

exception Error of Lexing.lexbuf

}

rule main = parse
  | [' ' '\t' '\r' '\n']+ { main lexbuf }
  | "*" { P.ASTER }
  | "@" { P.AT }
  | "%" { P.PERCENT }
  | ":" { P.COLON }
  | "$" { P.DOLLAR }
  | "?" { P.QUES }
  | "(" { P.LPAREN }
  | ")" { P.RPAREN }
  | "[" { P.LBRACKET }
  | "]" { P.RBRACKET }
  | "." { P.DOT }
  | "," { P.COMMA }
  | ['A'-'Z' 'a'-'z'] { P.VAR (Lexing.lexeme lexbuf) }
  | ['A'-'Z' 'a'-'z'] ['A'-'Z' 'a'-'z' '0'-'9' '_']+ { P.CVAR (Lexing.lexeme lexbuf) }
  | eof { P.EOF }
  | _ { raise (Error lexbuf) }
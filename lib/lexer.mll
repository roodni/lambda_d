{
module P = Parser

exception Error

}

rule main = parse
  | [' ' '\t' '\r']+ { main lexbuf }
  | "\n" { Lexing.new_line lexbuf; main lexbuf }
  | "*" { P.ASTER }
  | "@" { P.AT }
  | "%" { P.PERCENT }
  | ":" { P.COLON }
  | "=" { P.EQ }
  | ":=" { P.DEFEQ }
  | "$" { P.DOLLAR }
  | "?" { P.QUES }
  | "#" { P.HASH }
  | "(" { P.LPAREN }
  | ")" { P.RPAREN }
  | "[" { P.LBRACKET }
  | "]" { P.RBRACKET }
  | "{" { P.LBRACE }
  | "}" { P.RBRACE }
  | "." { P.DOT }
  | "," { P.COMMA }
  | ";" { P.SEMI }
  | ['A'-'Z' 'a'-'z'] { P.VAR (Named (Lexing.lexeme lexbuf)) }
  | ['A'-'Z' 'a'-'z'] ['A'-'Z' 'a'-'z' '0'-'9' '_']+ { P.CVAR (Lexing.lexeme lexbuf) }
  | eof { P.EOF }
  | _ { raise Error }
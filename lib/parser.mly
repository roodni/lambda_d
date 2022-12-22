%{
open Syntax
open Term
%}

%token ASTER
%token AT
%token PERCENT
%token COLON
%token DOLLAR
%token QUES

%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token DOT
%token COMMA

%token <Syntax.Var.t> VAR
%token <string> CVAR

%token EOF

%start main
%type <Term.t> main

%%

main:
  | t=term EOF { t }

term:
  | LPAREN t=term RPAREN { t }
  | ASTER { Star }
  | AT { Sort }
  | v=VAR { Var v }
  | PERCENT LPAREN t1=term RPAREN LPAREN t2=term RPAREN {
      App (t1, t2)
    }
  | DOLLAR v=VAR COLON LPAREN t1=term RPAREN DOT LPAREN t2=term RPAREN {
      Lambda (v, t1, t2)
    }
  | QUES v=VAR COLON LPAREN t1=term RPAREN DOT LPAREN t2=term RPAREN {
      Pai (v, t1, t2)
    }
  | cv=CVAR LBRACKET tl=separated_list(COMMA, term) RBRACKET {
      Const (cv, tl)
    }
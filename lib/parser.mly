%{
open Syntax
open Term
%}

%token ASTER
%token AT
%token PERCENT
%token COLON
%token EQ DEFEQ
%token DOLLAR
%token QUES
%token HASH
%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token LBRACE RBRACE
%token DOT
%token COMMA
%token SEMI

%token <Syntax.Var.t> VAR
%token <string> CVAR

%token EOF

%start main
%type <Term.t> main

%start deflang
%type <figure list> deflang

%%

// 授業文法
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

// Definition記述言語
deflang:
  | l=figure* EOF { l }

figure:
  | n=CVAR LBRACE l=figure_elm* RBRACE { (n, l) }

figure_elm:
  | n=CVAR LBRACKET vl=separated_list(COMMA, VAR) RBRACKET
      scope=def proof=proof COLON prop=term SEMI
    { Definition (scope, n, vl, proof, prop) }
  | b=separated_list(COMMA, binding) LBRACE l=figure_elm* RBRACE
    { Context (b, l) }

def:
  | EQ { `Local }
  | DEFEQ { `Global }

proof:
  | t=term { Some t }
  | HASH { None }

binding:
  | v=VAR COLON t=term { (v, t) }
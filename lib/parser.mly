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

%token DARROW

%token <Syntax.Var.t> VAR
%token <string> CVAR

%token EOF

%start main
%type <Term.t> main

%start deflang
%type <figure list> deflang

%%


main:
  | t=term EOF { t }

// 拡張授業文法
term:
  | t=term_appable { t }
  | DOLLAR v=VAR COLON t1=term DOT t2=term
    { Lambda (MaybeNF, v, t1, t2) }
  | QUES v=VAR COLON t1=term DOT t2=term
    { Pai (MaybeNF, v, t1, t2) }
  | l=term_appable DARROW r=term
    { Const (MaybeNF, "implies", [l; r]) }

term_appable:
  | t=term_simple { t }
  | l=term_appable r=term_simple { App (MaybeNF, l, r) }

term_simple:
  | LPAREN t=term RPAREN { t }
  | ASTER { Star }
  | AT { Square }
  | v=VAR { Var v }
  | PERCENT LPAREN t1=term RPAREN LPAREN t2=term RPAREN
    { App (MaybeNF, t1, t2) }
  | cv=CVAR LBRACKET tl=separated_list(COMMA, term) RBRACKET
    { Const (MaybeNF, cv, tl) }


// Definition記述言語
deflang:
  | l=figure* EOF { l }

figure:
  | n=CVAR LBRACE l=figure_elm* RBRACE { (n, l) }

figure_elm:
  | n=CVAR argdef=argdef scope=def proof=proof COLON prop=term SEMI
    { Definition (scope, n, argdef, proof, prop) }
  | b=separated_list(COMMA, binding) LBRACE l=figure_elm* RBRACE
    { Context (b, l) }

argdef:
  | LBRACKET vl=separated_list(COMMA, VAR) RBRACKET { Some vl }
  | { None }

def:
  | EQ { `Local }
  | DEFEQ { `Global }

proof:
  | t=term { Some t }
  | HASH { None }

binding:
  | v=VAR COLON t=term { (v, t) }
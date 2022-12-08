%{
open Syntax
%}

%token ASTER
%token AT

%start term
%type <term> term

%%

term:
  | ASTER { Kind }
  | AT { Sort }
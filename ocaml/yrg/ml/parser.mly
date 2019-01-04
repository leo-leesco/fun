(* -*- tuareg -*- *)

%{

let make_lam x t =
  Syntax.(ITerm.Lam (Name.fresh (fun _ -> x), t))

%}

%token<string> ID
%token<int> INT
%token LET EQUAL IN FUN RARROW EOF LPAREN RPAREN

%start<Syntax.ITerm.t> program

%nonassoc IN RARROW
%nonassoc LPAREN ID INT

%%

program: t=term EOF {
  t
}

term:
| t=term u=simple_term {
   Syntax.ITerm.App (t, u)
}
| LET x=ID EQUAL t=term IN u=term
{
   Syntax.(ITerm.Let (Name.fresh (fun _ -> x), t, u))
}
| FUN xs=ID+ RARROW t=term
{
  List.fold_right make_lam xs t
}
| t=simple_term
{
  t
}

simple_term:
| x=ID {
   Syntax.(ITerm.Var (Name.fresh (fun _ -> x)))
}
| x=INT {
   Syntax.(ITerm.Lit x)
}
| LPAREN t=term RPAREN
{
   t
}

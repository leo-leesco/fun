%token VAL "val"
%token DEF "def"
%token HANDLE "handle"
%token PRINT "Print"
%token FALSE TRUE
%token IF "if"
%token ELSE "else"
%token<string> VVAR "x"
%token<string> BVAR "F"
%token<string> STRING
%token EQ "="
%token SEMI ";"
%token COMMA ","
%token LPAR "("
%token RPAR ")"
%token LBRACE "{"
%token RBRACE "}"
%token EOF

%start<SystemXi.statement> phrase

%{

  open SystemXi

  (* SystemXi does not have a unit type. (It could have one, but I prefer
     to avoid that, as it might cause confusion with the tuples of arguments
     that one can pass to a block.) The following default value is used in
     situations where the unit value is normally used, e.g., when an [else]
     branch is missing. *)

  let default =
    ExBool true

%}

%%

let phrase :=
  ~ = statement; EOF; <>

let statement ==
  statement1

let statement1 :=
  srange (
      "val"; x = "x"; "="; s1 = statement0; ";"; s2 = statement1;
        { SLetVal (x, s1, s2) }
    | s1 = statement0; ";"; s2 = statement1;
        (* [s1; s2] is sugar for [val _ = s1; s2]. *)
        { SLetVal ("_", s1, s2) }
    | "def"; f = "F"; b = block; s = statement1;
        { SLetBlock (f, b, s) }
    | "if"; e = expression; s1 = statement0;
        { SIf (e, s1, SReturn default) }
    | "if"; e = expression; s1 = statement0; "else"; s2 = statement0;
        { SIf (e, s1, s2) }
  )
  | statement0

let statement0 :=
  srange (
    e = expression;
      { SReturn e }
  | "handle"; body = block; handler = block;
      { SHandle (body, handler) }
  | "Print"; e = parenthesized(expression);
      { SPrint e }
  )
  | braced(statement)

let srange(statement) ==
  s = statement;
    { SRange (($startpos, $endpos), s) }

let expression :=
  exrange (
    x = "x";
      { ExVar x }
  | FALSE;
      { ExBool false }
  | TRUE;
      { ExBool true }
  | s = STRING;
      { ExString s }
  | b = block0; actuals = actuals;
      { ECall (b, actuals) }
  )
  | parenthesized(expression)

let exrange(expression) ==
  e = expression;
    { ExRange (($startpos, $endpos), e) }

let block ==
  block1

let block1 :=
  brange (
    ~ = formals; ~ = braced(statement); <BlockDef>
  )
  | block0

let block0 ==
  brange (
  | ~ = "F"; <BlockVar>
  )

let brange(block) ==
  b = block;
    { BlockRange (($startpos, $endpos), b) }

let actuals ==
  parenthesized(separated_list(",", actual))

let actual :=
  | ~ = expression; <Value>
  | ~ = block0; <Block>

let formals ==
  parenthesized(separated_list(",", formal))

let formal :=
  | ~ = "x"; <Value>
  | ~ = "F"; <Block>

let parenthesized(X) ==
  "("; ~ = X; ")"; <>

let braced(X) ==
  "{"; ~ = X; "}"; <>

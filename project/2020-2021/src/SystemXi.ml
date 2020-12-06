(* This is the abstract syntax of System Xi. *)

(* A value variable is an identifier that begins with a lowercase letter. *)

type vvar =
  string

(* A block variable is an identifier that begins with an uppercase letter. *)

type bvar =
  string

(* The type [choice] is used in a few places to indicate a choice between
   the syntactic category of values and the syntactic category of blocks. *)

type ('v, 'b) choice =
  | Value of 'v
  | Block of 'b

(* A range is a pair of positions in a source file. It is used when
   reporting a type error or a runtime error. *)

type range =
  Lexing.position * Lexing.position

(* The syntactic category of statements is roughly as in Figure 3a of
   Brachthäuser et al.'s paper. One small difference is that a function
   call is viewed here as an expression; this is more expressive. *)

type statement =
  | SRange of range * statement
  | SLetVal of vvar * statement * statement
  | SReturn of expression
  | SLetBlock of bvar * block * statement
  | SHandle of block * block
  | SPrint of expression
  | SIf of expression * statement * statement

(* The syntactic category of expressions. *)

and expression =
  | ExRange of range * expression
  | ExVar of vvar
  | ExBool of bool
  | ExString of string
  | ECall of block * actuals

(* The syntactic category of blocks. *)

and block =
  | BlockRange of range * block
  | BlockVar of bvar
  | BlockDef of formals * statement

(* Actual arguments appear in function calls. An actual argument is
   either an expression or a block. *)

and actuals =
  actual list

and actual =
  (expression, block) choice

(* Formal arguments appear in function definitions. A formal argument
   is either a value variable or a block variable. *)

and formals =
  formal list

and formal =
  (vvar, bvar) choice

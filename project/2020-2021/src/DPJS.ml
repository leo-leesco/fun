(* This is the abstract syntax of the calculus DPJS. *)

type var =
  string

(* A range is a pair of positions in a source file. It is used when
   reporting a type error or a runtime error. *)

type range =
  Lexing.position * Lexing.position

type expr =
  | ERange of range * expr
  | EVar of var
  | ELam of var * expr
  | EApp of expr * expr
  | ELet of var * expr * expr
  | ETuple of expr list
  | ELetTuple of var list * expr * expr
  | ENewPrompt
  | EPushPrompt of expr * expr
  | EWithSubCont of expr * expr
  | EPushSubCont of expr * expr
  | EBool of bool
  | EIf of expr * expr * expr
  | EString of string
  | EPrint of expr

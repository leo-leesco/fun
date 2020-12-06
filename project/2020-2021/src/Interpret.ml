open Printf
open DPJS
open DelimitedContinuationMonad

(* Once you are done writing the code, remove this directive,
   whose purpose is to disable several warnings. *)
[@@@warning "-27-32-37-39"]

(* A runtime environment is a map of variables to values. *)

module Env = struct

  include Map.Make(String)

  let add_many (xs : var list) (vs : 'v list) (m : 'v t) : 'v t =
    assert (List.length xs = List.length vs);
    List.fold_right2 add xs vs m

end

(* This is the type of values. *)

type value =
  | VClosure of var * expr * env
  | VString of string
  | VTuple of value list
  (* TASK: complete this definition by adding more cases as needed. *)

and env =
  value Env.t

(* [print_value quote_strings v] transforms the value [v] into a string. If
   [quote_strings] is [true], then a value of the form [VString _] is printed
   as a string literal (with quotes); otherwise, only the string itself is
   printed (without quotes). *)

let rec print_value quote_strings v =
  match v with
  | VClosure _ ->
      "a closure"
  | VString s ->
      if quote_strings then
        sprintf "\"%s\"" (String.escaped s)
      else
        s
  | VTuple [] ->
      "()"
  | VTuple (v :: vs) ->
      let b = Buffer.create 128 in
      bprintf b "(%s" (print_value quote_strings v);
      List.iter (fun v -> bprintf b ", %s" (print_value quote_strings v)) vs;
      bprintf b ")";
      Buffer.contents b

(* [print_env b env] prints the environment [env] to the buffer [b]. *)

let print_env b env =
  bprintf b "\nHere is the interpreter's runtime environment:\n";
  Env.iter (fun x v ->
    bprintf b "  %s = %s\n" x (print_value true v)
  ) env;
  bprintf b "\n"

(* [error range env format ...] prints a runtime error message. *)

exception RuntimeError of range * string

let error env range format =
  let b = Buffer.create 128 in
  kbprintf (fun b ->
    print_env b env;
    let msg = Buffer.contents b in
    raise (RuntimeError (range, msg))
  ) b format

(* Looking for a variable in a runtime environment. *)

let find env range x =
  try
    Env.find x env
  with Not_found ->
    error env range "the variable %s is unbound.\n" x

(* The following are projection functions. They perform a runtime test
   (which can fail) and convert a value to a specific kind of value. *)

let asClosure env range v =
  match v with
  | VClosure (x, e, env) ->
      x, e, env
  | _ ->
      error env range "a closure was expected, but %s was found.\n"
        (print_value true v)

let asTuple env range arity v =
  match v with
  | VTuple vs when List.length vs = arity ->
      vs
  | VTuple _ ->
      error env range "a tuple of arity %d was expected, but %s was found.\n"
        arity (print_value true v)
  | _ ->
      error env range "a tuple was expected, but %s was found.\n"
        (print_value true v)

(* The main function of the interpreter [eval], interprets an expression [e]
   as a monadic computation, under a runtime environment [env]. The [range]
   parameter is used only when a runtime error occurs. *)

let rec eval env range (e : expr) : value m =
  match e with
  | ERange (range, e) ->
      eval env range e
  | EVar x ->
      return (find env range x)
  | ELam (x, e) ->
      (* We have a memory leak here: we could (should) keep an environment
         that is restricted to the free variables of [ELam (x, e)]. *)
      return (VClosure (x, e, env))
  | EApp (e1, e2) ->
      let* v1 = eval env range e1 in
      let* v2 = eval env range e2 in
      apply env range v1 v2
  | _ ->
      assert false (* TASK: implement the missing cases. *)

(* The auxiliary function [eval_many] evaluates a list of expressions,
   from left to right. Therefore, it returns a monadic computation whose
   result is a list of values. *)

and eval_many env range (es : expr list) : value list m =
  assert false (* TASK: implement this function. *)

and apply env range v1 v2 =
  let x, e, env = asClosure env range v1 in
  let env = Env.add x v2 env in
  eval env range e

(* The entry point. *)

let execute e =
  try
    let env = Env.empty in
    let range = Lexing.(dummy_pos, dummy_pos) in
    let (_v : value) = run (eval env range e) in
    ()
  with RuntimeError (range, msg) ->
    printf "RUNTIME ERROR\n";
    LexerUtil.print_range stderr range;
    eprintf "%s" msg;
    Printexc.print_backtrace stderr;
    exit 0

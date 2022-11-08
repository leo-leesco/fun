(* This code uses MetaOCaml: *)
(* https://okmij.org/ftp/ML/MetaOCaml.html#install *)

(* To interpret this file in the OCaml REPL,
   use [metaocaml] instead of [ocaml].
   Or the long form: [opam exec --switch 4.11.1+BER metaocaml]. *)

(* The following incantation is required for the type [code] to be known: *)
open Codelib

(* The following incantation is required for the function [run] to be known.
   Use [Runnative] when compiling to native code and [Runcode] when compiling
   to bytecode or interpreting this file in the OCaml REPL. *)
open Runnative
  (* in the REPL: open Runcode;; *)

(* -------------------------------------------------------------------------- *)

(* The MetaOCaml "Hello world": the power function. The use of this function
   as an introductory example goes back to Ershov (1977). *)

(* The square function is defined by [let square x = x * x]. *)

(* It is placed in a separate module, Square. Indeed, we will need to use
   this function at stage 2 (inside angle brackets .< ... >.) -- a feature
   that is known as cross-stage persistence (CSP). MetaOCaml restricts CSP
   to values that have been defined in separate modules. *)

open Square
  (* in the REPL: #load "Square.cmo";; *)

(* A staged power function. [cpower_aux n e] takes an integer [n] and an
   integer expression [e] -- in other words, a piece of code [e] that
   produces an integer value -- and returns an integer expression that
   represents [e^n]. *)

(* In each branch, it is important to use the expression returned by
   the recursive call [cpower_aux ... e] only once, as we would otherwise
   duplicate this expression. The use of [square] helps achieve this.
   The expression [e] is duplicated (in the second branch), which is
   potentially dangerous; this is acceptable here because [e] must be
   a variable (see [power] below). *)

(* Some intuition:

   [int] is an integer that is available now, in this stage;

   [int code] is an integer that will be available only in the next stage;

   but [int code] can also be understood as code of type [int]
   that is available now;

   and [int code -> int code] can be understood as code of type [int]
   with a single hole of type [int]. This is the type of [cpower_aux n]. *)

let rec cpower_aux (n : int) (e : int code) : int code =
  if n = 0 then .<1>.
  else if n mod 2 = 0 then .<square .~(cpower_aux (n/2) e)>.
  else .<.~e * .~(cpower_aux (n-1) e)>.
;;

(* To use [cpower_aux], we need to create a fresh variable [x] and apply
   [cpower_aux] to this variable. This is done as follows. *)

let cpower (n : int) : (int -> int) code =
  .< fun x -> .~(cpower_aux n .<x>.) >.
;;

(* [cpower n] has type [(int -> int) code]. It returns an expression
   that represents the function that maps [x] to its [n]-th power.
   For example, by fixing [n] to be 7, we get: *)

let cpower7 : (int -> int) code =
  cpower 7
;;

(* We can "run" this code to obtain an actual function of type [int -> int].
   Here, "running" the code does essentially nothing, since this code is a
   value (a function definition). What we are really doing is compile this
   code so as to obtain an executable function. (Yes, the OCaml compiler is
   present at runtime, and the code that it produces can be dynamically linked
   with the code that is already running.) *)

let power7 : int -> int =
  run cpower7
;;

let () =
  let candidate = power7 2 in
  if candidate = 128 then
    Printf.printf "Indeed, the 7th power of 2 is 128.\n%!"
  else
    Printf.printf "ERROR -- the 7th power of 2 is not %d.\n%!" candidate

(* The generated code can be printed as follows: *)

let () =
  print_code Format.std_formatter cpower7

(* The code looks like this:

   fun x -> x * (square (x * (square (x * 1))))

 *)

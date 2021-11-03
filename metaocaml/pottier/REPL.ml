(* To interpret this file in the OCaml REPL,
   use [metaocaml] instead of [ocaml].
   Or the long form: [opam exec --switch 4.11.1+BER metaocaml]. *)

(* If you type this in the [metaocaml] REPL, then you are ready to play
   with the code in Power.ml and StreamFusion.ml. You must type [make]
   first so that the .cmo files are available. *)

open Codelib;;
open Runcode;;
open Square;;
#load "Square.cmo";;
open Shape;;
#load "Shape.cmo";;

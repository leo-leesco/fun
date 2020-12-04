(* Once you are done writing the code, remove this directive,
   whose purpose is to disable several warnings. *)
[@@@warning "-27-32-33-37-39"]

open SystemXi
open DPJS

(* This is a generator of fresh variable names. *)

let postincrement c =
  let y = !c in
  c := y + 1;
  y

let fresh_var =
  let c = ref 0 in
  fun base ->
    Printf.sprintf "%s%d" base (postincrement c)

(* The following auxiliary functions help construct DPJS terms. *)

let (!) x =
  EVar x

let lambda x e =
  ELam (x, e)

let (@) e1 e2 =
  EApp (e1, e2)

let def x e1 e2 =
  ELet (x, e1, e2)

let pushPrompt p e =
  EPushPrompt (p, e)

let withSubContLambda p k e =
  EWithSubCont (p, ELam (k, e))

let pushSubCont k e =
  EPushSubCont (k, e)

let translate_statement s =
  assert false
  (* TASK: implement the translation. *)

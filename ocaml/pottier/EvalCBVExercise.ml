(* -------------------------------------------------------------------------- *)

(* The type of lambda-terms, in de Bruijn's representation. *)

type var = int (* a de Bruijn index *)
type term =
  | Var of var
  | Lam of (* bind: *) term
  | App of term * term
  | Let of (* bind: *) term * term

(* -------------------------------------------------------------------------- *)

(* An environment-based big-step interpreter. This is the same interpreter
   that we programmed in Coq, except here, in OCaml, fuel is not needed. *)

type cvalue =
  | Clo of (* bind: *) term * cenv

and cenv =
  cvalue list

let empty : cenv =
  []

exception RuntimeError

let lookup (e : cenv) (x : var) : cvalue =
  try
    List.nth e x
  with Failure _ ->
    raise RuntimeError

let rec eval (e : cenv) (t : term) : cvalue =
  match t with
  | Var x ->
      lookup e x
  | Lam t ->
      Clo (t, e)
  | App (t1, t2) ->
      let cv1 = eval e t1 in
      let cv2 = eval e t2 in
      let Clo (u1, e') = cv1 in
      eval (cv2 :: e') u1
  | Let (t1, t2) ->
      eval (eval e t1 :: e) t2

(* -------------------------------------------------------------------------- *)

(* The CPS-transformed interpreter. *)

let rec evalk (e : cenv) (t : term) (k : cvalue -> 'a) : 'a =
  assert false

let eval (e : cenv) (t : term) : cvalue =
  evalk e t (fun cv -> cv)

(* -------------------------------------------------------------------------- *)

(* The CPS-transformed, defunctionalized interpreter. *)

type kont

let rec evalkd (e : cenv) (t : term) (k : kont) : cvalue =
  assert false

and apply (k : kont) (cv : cvalue) : cvalue =
  assert false

let eval e t =
  evalkd e t (assert false)

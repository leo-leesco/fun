(* -------------------------------------------------------------------------- *)

(* The type of lambda-terms, in de Bruijn's representation. *)

type var = int (* a de Bruijn index *)
type term =
  | Var of var
  | Lam of (* bind: *) term
  | App of term * term
  | Let of (* bind: *) term * term

(* -------------------------------------------------------------------------- *)

(* Under a call-by-name regime, in a function call, the actual argument is not
   evaluated immediately; instead, a thunk is built (a pair of the argument
   and the environment in which it must be evaluated). Thus, an environment is
   a list of thunks. As in call-by-value, a closure is a pair of a term and an
   environment. (Closures and thunks differ in that a closure binds a
   variable, the formal argument, in the term. A thunk does not.) *)

type cvalue =
  | Clo of (* bind: *) term * cenv

and cenv =
  thunk list

and thunk =
  | Thunk of term * cenv

(* -------------------------------------------------------------------------- *)

(* Environments. *)

let empty : cenv =
  []

exception RuntimeError

let lookup (e : cenv) (x : var) : thunk =
  try
    List.nth e x
  with Failure _ ->
    raise RuntimeError

(* -------------------------------------------------------------------------- *)

(* An environment-based big-step call-by-name interpreter. *)

let rec eval (e : cenv) (t : term) : cvalue =
  match t with
  | Var x ->
      let Thunk (t, e) = lookup e x in
      eval e t
  | Lam t ->
      Clo (t, e)
  | App (t1, t2) ->
      let cv1 = eval e t1 in
      let Clo (u1, e') = cv1 in
      eval (Thunk(t2, e) :: e') u1
  | Let (t1, t2) ->
      eval (Thunk (t1, e) :: e) t2

(* -------------------------------------------------------------------------- *)

(* The CPS-transformed interpreter. *)

let rec evalk (e : cenv) (t : term) (k : cvalue -> 'a) : 'a =
  match t with
  | Var x ->
      let Thunk (t, e) = lookup e x in
      evalk e t k
  | Lam t ->
      k (Clo (t, e))
  | App (t1, t2) ->
      evalk e t1 (fun cv1 ->
      let Clo (u1, e') = cv1 in
      evalk (Thunk(t2, e) :: e') u1 k)
  | Let (t1, t2) ->
      evalk (Thunk (t1, e) :: e) t2 k

let eval (e : cenv) (t : term) : cvalue =
  evalk e t (fun cv -> cv)

(* -------------------------------------------------------------------------- *)

(* The CPS-transformed, defunctionalized interpreter. *)

type kont =
  | AppL of { e: cenv; t2: term; k: kont }
  | Init

let rec evalkd (e : cenv) (t : term) (k : kont) : cvalue =
  match t with
  | Var x ->
      let Thunk (t, e) = lookup e x in
      evalkd e t k
  | Lam t ->
      apply k (Clo (t, e))
  | App (t1, t2) ->
      evalkd e t1 (AppL { e; t2; k })
  | Let (t1, t2) ->
      evalkd (Thunk (t1, e) :: e) t2 k

and apply (k : kont) (cv : cvalue) : cvalue =
  match k with
  | AppL { e; t2; k } ->
      let cv1 = cv in
      let Clo (u1, e') = cv1 in
      evalkd (Thunk(t2, e) :: e') u1 k
  | Init ->
      cv

let eval (e : cenv) (t : term) : cvalue =
  evalkd e t Init

(* -------------------------------------------------------------------------- *)

(* Because [apply] has only one call site, it can be inlined, yielding a
   slightly more compact and readable definition. *)

let rec evalkd (e : cenv) (t : term) (k : kont) : cvalue =
  match t, k with
  | Var x, _ ->
      let Thunk (t, e) = lookup e x in
      evalkd e t k
  | Lam t, AppL { e; t2; k } ->
      let cv1 = Clo (t, e) in
      let Clo (u1, e') = cv1 in
      evalkd (Thunk(t2, e) :: e') u1 k
  | Lam t, Init ->
      Clo (t, e)
  | App (t1, t2), _ ->
      evalkd e t1 (AppL { e; t2; k })
  | Let (t1, t2), _ ->
      evalkd (Thunk (t1, e) :: e) t2 k

let eval (e : cenv) (t : term) : cvalue =
  evalkd e t Init

(* -------------------------------------------------------------------------- *)

(* The type [kont] is isomorphic to [(cenv * term) list]. Using the latter
   type makes the code slightly prettier, although slightly less efficient. *)

(* At this point, one recognizes Krivine's machine. *)

let rec evalkd (e : cenv) (t : term) (k : (cenv * term) list) : cvalue =
  match t, k with
  | Var x, _ ->
      let Thunk (t, e) = lookup e x in
      evalkd e t k
  | Lam t, (e, t2) :: k ->
      let cv1 = Clo (t, e) in
      let Clo (u1, e') = cv1 in
      evalkd (Thunk(t2, e) :: e') u1 k
  | Lam t, [] ->
      Clo (t, e)
  | App (t1, t2), _ ->
      evalkd e t1 ((e, t2) :: k)
  | Let (t1, t2), _ ->
      evalkd (Thunk (t1, e) :: e) t2 k

let eval (e : cenv) (t : term) : cvalue =
  evalkd e t []

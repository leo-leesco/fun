(* -------------------------------------------------------------------------- *)

(* The type of lambda-terms, in de Bruijn's representation. *)

type var = int (* a de Bruijn index *)
type term =
  | Var of var
  | Lam of (* bind: *) term
  | App of term * term
  | Let of (* bind: *) term * term

(* -------------------------------------------------------------------------- *)

(* [lift_ i k] represents the substitution [upn i (ren (+k))]. Its effect is to
   add [k] to every variable that occurs free in [t] and whose index is at
   least [i]. *)

let rec lift_ i k (t : term) : term =
  match t with
  | Var x ->
      if x < i then t else Var (x + k)
  | Lam t ->
      Lam (lift_ (i + 1) k t)
  | App (t1, t2) ->
      App (lift_ i k t1, lift_ i k t2)
  | Let (t1, t2) ->
      Let (lift_ i k t1, lift_ (i + 1) k t2)

(* [lift k t] adds [k] to every variable that occurs free in [t]. *)

let lift k t =
  lift_ 0 k t

(* [subst i sigma] represents the substitution [upn i sigma]. *)

let rec subst_ i (sigma : var -> term) (t : term) : term =
  match t with
  | Var x ->
      if x < i then t else lift i (sigma (x - i))
  | Lam t ->
      Lam (subst_ (i + 1) sigma t)
  | App (t1, t2) ->
      App (subst_ i sigma t1, subst_ i sigma t2)
  | Let (t1, t2) ->
      Let (subst_ i sigma t1, subst_ (i + 1) sigma t2)

(* [subst sigma t] applies the substitution [sigma] to the term [t]. *)

let subst sigma t =
  subst_ 0 sigma t

(* A singleton substitution [u .: ids]. *)

let singleton (u : term) : var -> term =
  function 0 -> u | x -> Var (x - 1)

(* -------------------------------------------------------------------------- *)

(* Recognizing a value. *)

let is_value = function
  | Var _ -> assert false (* we work with closed terms only *)
  | Lam _ -> true
  | App _ -> false
  | Let _ ->
     false

(* -------------------------------------------------------------------------- *)

(* Auxiliary functions: [fail], [return] and [bind] are the three basic
   operations of the [option] monad. *)

(* The last line allows writing [let* x = e1 in e2] as syntactic sugar
   for [bind e1 (fun x -> e2)]. *)

let fail : 'a option =
  None
let return (x : 'a) : 'a option =
  Some x
let bind (ox : 'a option) (f : 'a -> 'b option) : 'b option =
  match ox with
  | None ->   None
  | Some x -> f x
let (let*) = bind

(* -------------------------------------------------------------------------- *)

(* Stepping in call-by-value. *)

(* This is a naive, direct implementation of the call-by-value reduction
   relation, following Plotkin's formulation. The function [step t] returns
   [Some t'] if and only if the relation [cbv t t'] holds, and returns [None]
   if no such term [t'] exists. *)

let rec step (t : term) : term option =
  match t with
  | Lam _ | Var _ -> fail
  | App (Lam t, v) when is_value v ->   (* Plotkin's BetaV *)
      return (subst (singleton v) t)
  | App (t, u) when not (is_value t) -> (* Plotkin's AppL  *)
      let* t' = step t in
      return (App (t', u))
  | App (v, u) when is_value v ->       (* Plotkin's AppVR *)
      let* u' = step u in
      return (App (v, u'))
  | App (_, _) ->             (* All cases covered already *)
      assert false            (*  but OCaml cannot see it. *)
  | Let (t, u) when not (is_value t) ->
      let* t' = step t in
      return (Let (t', u))
  | Let (v, u) when is_value v ->
      return (subst (singleton v) u)
  | Let (_, _) ->
      assert false

let rec eval (t : term) : term =
  match step t with
  | None ->
      t
  | Some t' ->
      eval t'

(* -------------------------------------------------------------------------- *)

(* A naive, substitution-based big-step interpreter. *)

exception RuntimeError
let rec eval (t : term) : term =
  match t with
  | Lam _ | Var _ -> t
  | Let (t1, t2) ->
      let v1 = eval t1 in
      eval (subst (singleton v1) t2)
  | App (t1, t2) ->
      let v1 = eval t1 in
      let v2 = eval t2 in
      match v1 with
      | Lam u1 -> eval (subst (singleton v2) u1)
      | _      -> raise RuntimeError

(* -------------------------------------------------------------------------- *)

(* A term printer. *)

open Printf

let rec print f = function
  | Var x ->
      fprintf f "(Var %d)" x
  | Lam t ->
      fprintf f "(Lam %a)" print t
  | App (t1, t2) ->
      fprintf f "(App %a %a)" print t1 print t2
  | Let (t1, t2) ->
      fprintf f "(Let %a %a)" print t1 print t2

let print t =
  fprintf stdout "%a\n" print t

(* -------------------------------------------------------------------------- *)

(* Test. *)

let id =
  Lam (Var 0)

let idid =
  App (id, id)

let () =
  match step idid with
  | None ->
      assert false
  | Some reduct ->
      print reduct

let () =
  print (eval idid)

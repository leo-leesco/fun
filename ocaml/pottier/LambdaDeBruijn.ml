(* -------------------------------------------------------------------------- *)

(* The type of lambda-terms, in de Bruijn's representation. *)

type var = int (* a de Bruijn index *)
type binder = unit

type term =
  | Var of var
  | Lam of (* bind: *) term
  | App of term * term
  | Let of term * (* bind: *) term

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

exception Irreducible
let rec step (t : term) : term =
  match t with
  | Lam _ | Var _ ->
      raise Irreducible
  | App (Lam t, v) when is_value v ->   (* Plotkin's BetaV *)
      subst (singleton v) t
  | App (t, u) when not (is_value t) -> (* Plotkin's AppL  *)
      let t' = step t in App (t', u)
  | App (v, u) when is_value v ->       (* Plotkin's AppVR *)
      let u' = step u in App (v, u')
  | App (_, _) ->             (* All cases covered already *)
      assert false            (*  but OCaml cannot see it. *)
  | Let (t, u) when not (is_value t) ->
      let t' = step t in Let (t', u)
  | Let (v, u) when is_value v ->
      subst (singleton v) u
  | Let (_, _) ->
      assert false

let rec eval (t : term) : term =
  match step t with
  | exception Irreducible ->
      t
  | t' ->
      eval t'

(* -------------------------------------------------------------------------- *)

(* A naive, substitution-based big-step interpreter. *)

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
      | _      -> assert false (* every value is a function *)

(* -------------------------------------------------------------------------- *)

(* A term printer. *)

open Printf

module Print = struct

  let var f x =
    fprintf f "%d" x

  let rec term f = function
    | Var x ->
        fprintf f "(Var %a)" var x
    | Lam t ->
        fprintf f "(Lam %a)" term t
    | App (t1, t2) ->
        fprintf f "(App %a %a)" term t1 term t2
    | Let (t1, t2) ->
        fprintf f "(Let %a %a)" term t1 term t2

end

let print t =
  fprintf stdout "%a\n" Print.term t

(* -------------------------------------------------------------------------- *)

(* Test. *)

let id =
  Lam (Var 0)

let idid =
  App (id, id)

(* I am ashamed of the triviality of this unit test. *)
let () =
  assert (eval idid = id)

(* Some output. *)
let () =
  print (eval idid)

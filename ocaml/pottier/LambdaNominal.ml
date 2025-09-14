(* -------------------------------------------------------------------------- *)

(* The type of lambda-terms, in nominal representation. *)

(* A name is an integer. (One could use strings, which can be more readable;
   but integers are faster and make fresh name generation easy.) *)

type name = int
type var = name
type binder = name
type term =
  | Var of var
  | Lam of binder * term
  | App of term * term
  | Let of binder * term * term

(* -------------------------------------------------------------------------- *)

(* The set of free variables of a term. *)

open Set.Make(Int)

let rec fv t =
  match t with
  | Var x ->
      singleton x
  | Lam (x, t) ->
      remove x (fv t)
  | App (t1, t2) ->
      union (fv t1) (fv t2)
  | Let (x, t1, t2) ->
      union (fv t1) (remove x (fv t2))

(* A closed term is a term that does not have any free variables. *)

let closed t =
  is_empty (fv t)

(* -------------------------------------------------------------------------- *)

(* [subst x v t] is the result of replacing the variable [x] with the
   term [v] in the term [t]. *)

(* Here, for simplicity, we restrict our attention to the case where [v] is
   closed. In this special case, capture-avoiding substitution is easy: it
   is never necessary to rename a bound variable. Therefore it is never
   necessary to generate a fresh name. *)

let rec subst (x : var) (v : term) (t : term) : term =
  match t with
  | Var y ->
      if y <> x then Var y else v
  | Lam (y, t) ->
      Lam (y, if y = x then t else subst x v t)
  | App (t1, t2) ->
      App (subst x v t1, subst x v t2)
  | Let (y, t1, t2) ->
      Let (y, subst x v t1, if y = x then t2 else subst x v t2)

let subst x v t =
  assert (closed v); (* a sanity check *)
  subst x v t

(* -------------------------------------------------------------------------- *)

(* Determining whether two terms are alpha-equivalent. *)

(* This is not needed during reduction, but we can be useful in other places.
   We use this test in an assertion at the end of this file. *)

(* The simplest (efficient) way of performing this test is to convert both
   terms to a representation that uses de Bruijn levels, then compare them
   using ordinary equality.

   de Bruijn levels are the same as de Bruijn indices, except binders are
   numbered in the reverse direction. The outermost binder is 0; the next
   binder, going down, is 1; and so on.

   We perform the two conversions and the comparison on the fly, without
   explicitly building the two terms in de-Bruijn-level representation. To
   perform the two conversions, we carry two maps of names to de Bruijn
   levels, [env1] and [env2], as well as the next available level, [c].

   The complexity of our implementation is O(n.log k) where [n] is the size
   of the terms and [k] is their binding depth (that is, the maximum number
   of nested binders). By using hash tables instead of balanced binary trees,
   one could achieve complexity O(n). *)

open Map.Make(Int)
type level = int
type env = level t (* a map of names to de Bruijn levels *)

let rec aeq (env1 : env) (env2 : env) (c : level) (t1 : term) (t2 : term) =
  match t1, t2 with
  | Var x1, Var x2 ->
    (
      match find_opt x1 env1, find_opt x2 env2 with
      | Some l1, Some l2 ->
          (* Both names are bound. *)
          l1 = l2
      | None, None ->
          (* Both names are free. *)
          x1 = x2
      | None, Some _
      | Some _, None ->
          (* One name is bound, the other is free. *)
          false
    )
  | Lam (x1, t1), Lam (x2, t2) ->
      (* Allocate the next de Bruijn level. *)
      let env1 = add x1 c env1
      and env2 = add x2 c env2
      and c = c + 1 in
      (* Compare the function bodies. *)
      aeq env1 env2 c t1 t2
  | App (t1a, t1b), App (t2a, t2b) ->
      aeq env1 env2 c t1a t2a &&
      aeq env1 env2 c t1b t2b
  | Let (x1, t1a, t1b), Let (x2, t2a, t2b) ->
      aeq env1 env2 c t1a t2a &&
      aeq env1 env2 c (Lam (x1, t1b)) (Lam (x2, t2b)) (* a shortcut *)
  | _, _ ->
      false

let aeq (t1 : term) (t2 : term) : bool =
  aeq empty empty 0 t1 t2

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
  | App (Lam (x, t), v) when is_value v -> (* Plotkin's BetaV *)
      subst x v t
  | App (t, u) when not (is_value t) ->    (* Plotkin's AppL  *)
      let t' = step t in App (t', u)
  | App (v, u) when is_value v ->          (* Plotkin's AppVR *)
      let u' = step u in App (v, u')
  | App (_, _) ->                (* All cases covered already *)
      assert false               (*  but OCaml cannot see it. *)
  | Let (x, t, u) when not (is_value t) ->
      let t' = step t in Let (x, t', u)
  | Let (x, v, u) when is_value v ->
      subst x v u
  | Let (_, _, _) ->
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
  | Let (x, t1, t2) ->
      let v1 = eval t1 in
      eval (subst x v1 t2)
  | App (t1, t2) ->
      let v1 = eval t1 in
      let v2 = eval t2 in
      match v1 with
      | Lam (x, u1) -> eval (subst x v2 u1)
      | _           -> assert false (* every value is a function *)

(* -------------------------------------------------------------------------- *)

(* A term printer. *)

open Printf

module Print = struct

  let var f x =
    fprintf f "%d" x

  let rec term f = function
    | Var x ->
        fprintf f "(Var %a)" var x
    | Lam (x, t) ->
        fprintf f "(Lam %a %a)" var x term t
    | App (t1, t2) ->
        fprintf f "(App %a %a)" term t1 term t2
    | Let (x, t1, t2) ->
        fprintf f "(Let %a %a %a)" var x term t1 term t2

end

let print t =
  fprintf stdout "%a\n" Print.term t

(* -------------------------------------------------------------------------- *)

(* Test. *)

(* The identity term has multiple representations, because the name of the
   bound variable is arbitrary. *)

let mkid (x : name) : term = Lam (x, Var x)
let id0 : term = mkid 0
let id1 : term = mkid 1
let () = assert (aeq id0 id1)

let idid =
  App (id0, id1)

(* I am ashamed of the triviality of this unit test. *)
let () =
  assert (aeq (eval idid) (mkid 2))

(* Some output. *)
let () =
  print (eval idid)

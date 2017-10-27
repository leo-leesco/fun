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

(* Term/value/environment printers. *)

open Printf

let rec print_term f = function
  | Var x ->
      fprintf f "(Var %d)" x
  | Lam t ->
      fprintf f "(Lam %a)" print_term t
  | App (t1, t2) ->
      fprintf f "(App %a %a)" print_term t1 print_term t2
  | Let (t1, t2) ->
      fprintf f "(Let %a %a)" print_term t1 print_term t2

let rec print_cvalue f = function
  | Clo (t, e) ->
      fprintf f "< %a | %a >" print_term t print_cenv e

and print_cenv f = function
  | [] ->
      fprintf f "[]"
  | cv :: e ->
      fprintf f "%a :: %a" print_cvalue cv print_cenv e

let print_cvalue cv =
  fprintf stdout "%a\n" print_cvalue cv

(* -------------------------------------------------------------------------- *)

(* A tiny test suite. *)

let id =
  Lam (Var 0)

let idid =
  App (id, id)

let apply =
  Lam (Lam (App (Var 1, Var 0)))

let test1 eval t =
  print_cvalue (eval empty t)

let test name eval =
  printf "Testing %s...\n%!" name;
  test1 eval idid;
  test1 eval (App (apply, id));
  test1 eval (App (App (apply, id), id));
  ()

(* -------------------------------------------------------------------------- *)

(* Test. *)

let () =
  test "the direct-style evaluator" eval

(* -------------------------------------------------------------------------- *)

(* A CPS-transformed, environment-based big-step interpreter. *)

(* In this code, every recursive call to [evalk] is a tail call. Thus,
   it is compiled by the OCaml compiler to a loop, and requires only O(1)
   space on the OCaml stack. *)

let rec evalk (e : cenv) (t : term) (k : cvalue -> 'a) : 'a =
  match t with
  | Var x ->
      k (lookup e x)
  | Lam t ->
      k (Clo (t, e))
  | App (t1, t2) ->
      evalk e t1 (fun cv1 ->
      evalk e t2 (fun cv2 ->
      let Clo (u1, e') = cv1 in
      evalk (cv2 :: e') u1 k))
  | Let (t1, t2) ->
      evalk e t1 (fun cv1 ->
      evalk (cv1 :: e) t2 k)

(* It is possible to explicitly assert that these calls are tail calls.
   The compiler would tell us if we were wrong. *)

let rec evalk (e : cenv) (t : term) (k : cvalue -> 'a) : 'a =
  match t with
  | Var x ->
      (k[@tailcall]) (lookup e x)
  | Lam t ->
      (k[@tailcall]) (Clo (t, e))
  | App (t1, t2) ->
      (evalk[@tailcall]) e t1 (fun cv1 ->
      (evalk[@tailcall]) e t2 (fun cv2 ->
      let Clo (u1, e') = cv1 in
      (evalk[@tailcall]) (cv2 :: e') u1 k))
  | Let (t1, t2) ->
      (evalk[@tailcall]) e t1 (fun cv1 ->
      (evalk[@tailcall]) (cv1 :: e) t2 k)

let eval (e : cenv) (t : term) : cvalue =
  evalk e t (fun cv -> cv)

(* -------------------------------------------------------------------------- *)

(* Test. *)

let () =
  test "the CPS evaluator" eval

(* -------------------------------------------------------------------------- *)

(* The above code uses heap-allocated closures, which form a linked list in the
   heap. In fact, the interpreter's "stack" is now heap-allocated. To see this
   more clearly, let us defunctionalize the CPS-transformed interpreter. *)

(* There are four places in the above code where an anonymous continuation is
   built, so defunctionalization yields a data type of four possible kinds of
   continuations. This data type describes a linked list of stack frames! *)

type kont =
  | AppL of { e: cenv; t2: term; k: kont }
  | AppR of {       cv1: cvalue; k: kont }
  | LetL of { e: cenv; t2: term; k: kont }
  | Init

let rec evalkd (e : cenv) (t : term) (k : kont) : cvalue =
  match t with
  | Var x ->
      apply k (lookup e x)
  | Lam t ->
      apply k (Clo (t, e))
  | App (t1, t2) ->
      evalkd e t1 (AppL { e; t2; k })
  | Let (t1, t2) ->
      evalkd e t1 (LetL { e; t2; k })

and apply (k : kont) (cv : cvalue) : cvalue =
  match k with
  | AppL { e; t2; k } ->
      let cv1 = cv in
      evalkd e t2 (AppR { cv1; k })
  | AppR { cv1; k } ->
      let cv2 = cv in
      let Clo (u1, e') = cv1 in
      evalkd (cv2 :: e') u1 k
  | LetL { e; t2; k } ->
      let cv1 = cv in
      evalkd (cv1 :: e) t2 k
  | Init ->
      cv

let eval e t =
  evalkd e t Init

(* -------------------------------------------------------------------------- *)

(* Test. *)

let () =
  test "the defunctionalized CPS evaluator" eval

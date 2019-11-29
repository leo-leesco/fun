Require Import Option List MyTactics.
Require Import LambdaCalculusSyntax.
Require Import LambdaCalculusFreeVars.
Require Import LambdaCalculusBigStep.
Require Import LambdaCalculusInterpreter.

(* This is a CPS-style variant of our interpreter for the lambda-calculus.
   It was contributed by Basile Pesin. *)

(* Because this interpreter is fuel-based, its answer type must be of the
   form [option A]. *)

Fixpoint interpretk {A} n e t (k : cvalue -> option A) : option A :=
  match n with
  | 0 => None
  | S n =>
    match t with
    | Var x =>
        k (nth x e dummy_cvalue)
    | Lam t =>
        k (Clo t e)
    | App t1 t2 =>
        interpretk n e t1 (fun cv1 =>
        interpretk n e t2 (fun cv2 =>
        let '(Clo u1 e') := cv1 in
        interpretk n (cv2 :: e') u1 k))
    | Let t1 t2 =>
        interpretk n e t1 (fun cv1 =>
        interpretk n (cv1 :: e) t2 k)
    end
  end.

(* The CPS-style interpreter computes the same thing as the original
   interpreter. More precisely, calling the CPS-style interpreter with
   a continuation [k] is the same as using the original interpreter
   and passing its result (extracted out of the option monad) to [k]. *)

Lemma interpretk_interpret:
  forall {A} n e t (k : cvalue -> option A),
  interpretk n e t k =
  (interpret n e t) >>= k.
Proof.
  induction n; intros; simpl.
  (* No fuel. *)
  { reflexivity. }
  (* Some fuel. *)
  destruct t; simpl.
  (* Var. *)
  { auto. }
  (* Lam. *)
  { auto. }
  (* App. *)
  { rewrite IHn by auto.
    destruct (interpret n e t1); auto. simpl.
    rewrite IHn by auto.
    destruct (interpret n e t2); auto. simpl.
    destruct c. auto. }
  (* Let. *)
  { rewrite IHn by auto.
    destruct (interpret n e t); auto. simpl.
    auto. }
Qed.

(* The above statement can be specialized to the identity continuation. *)

Lemma interpretk_interpret_identity:
  forall n e t,
  interpretk n e t (fun x => Some x) =
  interpret n e t.
Proof.
  intros n e t.
  rewrite interpretk_interpret.
  destruct (interpret n e t); reflexivity.
Qed.

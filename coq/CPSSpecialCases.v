Require Import MyTactics.
Require Import LambdaCalculusSyntax.
Require Import LambdaCalculusValues.
Require Import CPSDefinition.
Require Import CPSContextSubstitution.
Require Import CPSKubstitution.

(* The translation of an application whose left-hand side is a value. *)

Lemma cps_app_value:
  forall v1 t2 c,
  is_value v1 ->
  cps (App v1 t2) c =
  cps t2 (M (App (App (lift 1 (cpsv v1)) (Var 0)) (lift 1 (reify c)))).
Proof.
  intros. cps. simpl.
  rewrite cps_kubstitution_0. asimpl.
  reflexivity.
Qed.

(* The translation of a value-value application. *)

Lemma cps_app_value_value:
  forall v1 v2 c,
  is_value v1 ->
  is_value v2 ->
  cps (App v1 v2) c =
  App (App (cpsv v1) (cpsv v2)) (reify c).
Proof.
  intros.
  rewrite cps_app_value by obvious.
  rewrite cps_value by eauto. asimpl.
  reflexivity.
Qed.

(* The translation of a [Let] construct whose left-hand side is a value. *)

Lemma cps_let_value:
  forall v1 t2 c,
  is_value v1 ->
  cps (Let v1 t2) c =
  Let (cpsv v1) (cps t2 (liftc 1 c)).
Proof.
  intros. cps. simpl. f_equal.
  eapply cps_kubstitution. (* [cps_substitution] could be used too *)
  { autosubst. }
  { rewrite substc_substc. autosubst. }
Qed.

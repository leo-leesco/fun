Require Import MyTactics.
Require Import LambdaCalculusSyntax.
Require Import LambdaCalculusValues.
Require Import CPSDefinition.

(* This file contains a few lemmas about [substc]. *)

(* Two successive applications of [substc] can be fused. *)

Lemma substc_substc:
  forall sigma1 sigma2 c,
  substc sigma2 (substc sigma1 c) = substc (sigma1 >> sigma2) c.
Proof.
  intros. destruct c; autosubst.
Qed.

(* Two successive applications of [liftc] can be fused. *)

Lemma liftc_liftc:
  forall i j c,
  liftc i (liftc j c) = liftc (i + j) c.
Proof.
  intros i j c. destruct c; autosubst.
Qed.

(* [apply] commutes with substitutions. *)

Lemma apply_substitution:
  forall c sigma c' v,
  substc sigma c = c' ->
  (apply c v).[sigma] = apply c' v.[sigma].
Proof.
  intros. subst. destruct c; autosubst.
Qed.

(* [reify] commutes with substitutions. *)

Lemma reify_substitution:
  forall c sigma c',
  substc sigma c = c' ->
  (reify c).[sigma] = reify c'.
Proof.
  intros. subst. destruct c; reflexivity.
Qed.

(* As a special case, [reify] commutes with lifting. *)

Lemma lift_reify:
  forall i c,
  lift i (reify c) = reify (liftc i c).
Proof.
  intros. destruct c; reflexivity.
Qed.

(* [substc] is preserved by [liftc]. *)

Lemma substc_liftc_liftc:
  forall i c sigma c',
  substc sigma c = c' ->
  substc (upn i sigma) (liftc i c) = liftc i c'.
Proof.
  intros. subst. destruct c; simpl.
  { rewrite lift_upn by tc. reflexivity. }
  { asimpl. erewrite plus_upn by tc. autosubst. }
Qed.

Global Hint Resolve substc_liftc_liftc : obvious.

(* As is the case for terms, lifting [c] by 1, then applying a substitution
   of the form [v .: ids], yields [c] again. *)

Lemma substc_liftc_single:
  forall c v,
  substc (v .: ids) (liftc 1 c) = c.
Proof.
  intros. destruct c; autosubst.
Qed.

(* Similarly, lifting [c] by 2, then applying a substitution of the form
   [v1 .: v2 .: ids], yields [c] again. *)

Lemma substc_liftc_double:
  forall c v1 v2,
  substc (v1 .: v2 .: ids) (liftc 2 c) = c.
Proof.
  intros. destruct c; autosubst.
Qed.

Require Import MyTactics.
Require Import LambdaCalculusSyntax.
Require Import LambdaCalculusValues.
Require Import CPSDefinition.
Require Import CPSContextSubstitution.
Require Import CPSRenaming.

(* The [substitution] lemma in CPSSubstitution pushes a substitution
   into [cps t k]. The substitution is pushed into both [t] and [k].
   Because it is pushed into [t], this substitution must be of the
   form [sigma >>> cpsv], so that, once pushed into [t], it becomes
   just [sigma]. *)

(* Here, we prove another substitution lemma, where the substitution
   need not be of the form [sigma >>> cpsv]. It can be an arbitrary
   substitution. We require [sigma] to not affect the term [t], so
   [sigma] is not pushed into [t]: it is pushed into [k] only. For
   this reason, we refer to this lemma as the [kubstitution] lemma.

   In order to express the idea that [sigma] does not affect a term,
   more precisely, we write this term under the form [t.[theta]]
   and we require that [theta] and [sigma] cancel out, that is,

     theta >> sigma = ids

   (This condition implies [is_ren theta], that is, [theta] must be
   a renaming.) Then, we are able to prove the following result:

     (cps t.[theta] (O k)).[sigma] = cps t (O k.[sigma])

   That is, the substitution [sigma], when pushed into [t], meets [theta]
   and they cancel out. *)

(* [apply] commutes with kubstitutions. *)

Lemma apply_kubstitution:
  forall c theta sigma c' v,
  theta >> sigma = ids ->
  substc sigma c = c' ->
  (apply c v.[theta]).[sigma] = apply c' v.
Proof.
  intros. subst.
  destruct c; asimpl; pick @eq ltac:(fun h => rewrite h); autosubst.
Qed.

Local Hint Resolve up_theta_sigma_ids : obvious.

(* The main result: [cpsv] and [cps] commute with kubstitutions. *)

Lemma kubstitution:
  (
    forall v theta sigma,
    theta >> sigma = ids ->
    (cpsv v.[theta]).[sigma] = cpsv v
  ) /\ (
    forall t c theta sigma c',
    theta >> sigma = ids ->
    substc sigma c = c' ->
    (cps t.[theta] c).[sigma] = cps t c'
  ).
Proof.
  eapply mutual_induction.
  (* [cpsv] *)
  { intros n IHcps v Hvn theta sigma Hid. clear IHcps.
    rewrite <- cpsv_renaming by obvious.
    asimpl. rewrite Hid.
    asimpl. reflexivity. }
  (* [cps] *)
  { intros n IHcpsv IHcps t c Htn theta sigma c' Hid Hkubstc. clear IHcpsv.
    value_or_app_or_let t; asimpl; cps.
    (* Case: [t] is a value. *)
    { rewrite <- cpsv_renaming by obvious.
      eauto using apply_kubstitution. }
    (* Case: [t] is an application. *)
    { eapply IHcps; obvious.
      simpl. f_equal.
      erewrite <- lift_up by tc.
      eapply IHcps; obvious.
      asimpl. do 2 f_equal.
      rewrite lift_reify.
      eapply reify_substitution.
      subst. rewrite substc_substc.
      reflexivity. }
    (* Case: [t] is a [let] construct. *)
    { eapply IHcps; obvious.
      simpl. do 2 f_equal.
      rewrite fold_up_up.
      rewrite up_sigma_up_ren by tc. simpl.
      eapply IHcps; obvious. }
  }
Qed.

(* The projections of the above result. *)

Definition cpsv_kubstitution := proj1 kubstitution.
Definition cps_kubstitution  := proj2 kubstitution.

(* A corollary where the substitution [sigma] is [v .: ids], that is, a
   substitution of the value [v] for the variable 0. *)

Lemma cps_kubstitution_0:
  forall t c v,
  (cps (lift 1 t) c).[v/] = cps t (substc (v .: ids) c).
Proof.
  intros. eapply cps_kubstitution.
  { autosubst. }
  { reflexivity. }
Qed.

(* A corollary where the substitution [sigma] is [up (v .: ids)], that is, a
   substitution of the value [v] for the variable 1. *)

Lemma cps_kubstitution_1:
  forall t c v,
  (cps t.[up (ren (+1))] c).[up (v .: ids)] = cps t (substc (up (v .: ids)) c).
Proof.
  intros. eapply cps_kubstitution.
  { autosubst. }
  { reflexivity. }
Qed.

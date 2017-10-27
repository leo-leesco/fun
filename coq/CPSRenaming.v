Require Import MyTactics.
Require Import LambdaCalculusSyntax.
Require Import LambdaCalculusValues.
Require Import CPSDefinition.
Require Import CPSContextSubstitution.

(* The CPS transformation commutes with renamings, where a renaming [sigma] is
   a substitution that maps variables to variables. (Note that [sigma] is not
   necessarily injective.) *)

Lemma renaming:
  (
    forall v sigma,
    is_ren sigma ->
    (cpsv v).[sigma] = cpsv v.[sigma]
  ) /\ (
    forall t c sigma c',
    is_ren sigma ->
    substc sigma c = c' ->
    (cps t c).[sigma] = cps t.[sigma] c'
  ).
Proof.
  eapply mutual_induction.
  (* [cpsv] *)
  { intros n IHcps v Hvn sigma Hsigma.
    destruct v; asimpl; cpsv; asimpl; try reflexivity.
    (* [Var] *)
    (* The CPS transformation maps variables to variables. *)
    { destruct Hsigma as [ xi ? ]. subst sigma. reflexivity. }
    (* [Lam] *)
    { erewrite IHcps by obvious. asimpl. reflexivity. }
  }
  (* [cps] *)
  { intros n IHcpsv IHcps t c Htn sigma c' Hsigma Hsubstc.
    (* Perform case analysis on [t]. The first two cases, [Var] and [Lam],
       can be shared by treating the case where [t] is a value. *)
    value_or_app_or_let t; asimpl; cps.
    (* Case: [t] is a value. *)
    { erewrite apply_substitution by eauto.
      rewrite IHcpsv by obvious.
      reflexivity. }
    (* Case: [t] is an application. *)
    { eapply IHcps; obvious.
      erewrite <- lift_upn by tc.
      simpl. f_equal.
      eapply IHcps; obvious.
      simpl.
      rewrite fold_up_upn, lift_upn by tc.
      do 3 f_equal.
      eauto using reify_substitution. }
    (* Case: [t] is a [let] construct. *)
    { eapply IHcps; obvious.
      simpl. do 2 f_equal.
      rewrite fold_up_up.
      erewrite IHcps by first [ eapply substc_liftc_liftc; eauto | obvious ].
      autosubst. }
  }
Qed.

(* The projections of the above result. *)

Definition cpsv_renaming := proj1 renaming.
Definition cps_renaming  := proj2 renaming.

(* A point-free reformulation of the above result: [cpsv] commutes with
   an arbitrary renaming [xi]. *)

Goal
  forall sigma,
  is_ren sigma ->
  cpsv >>> subst sigma = subst sigma >>> cpsv.
Proof.
  intros. f_ext; intros t. asimpl. eauto using cpsv_renaming.
Qed.

(* Corollaries. *)

Lemma up_sigma_cpsv:
  forall sigma,
  up (sigma >>> cpsv) = up sigma >>> cpsv.
Proof.
  eauto using up_sigma_f, cpsv_renaming with is_ren typeclass_instances.
Qed.

Lemma upn_sigma_cpsv:
  forall i sigma,
  upn i (sigma >>> cpsv) = upn i sigma >>> cpsv.
Proof.
  eauto using upn_sigma_f, cpsv_renaming with is_ren typeclass_instances.
Qed.

Hint Resolve up_sigma_cpsv upn_sigma_cpsv : obvious.

Require Import MyTactics.
Require Import LambdaCalculusSyntax.
Require Import LambdaCalculusValues.
Require Import CPSDefinition.
Require Import CPSContextSubstitution.
Require Import CPSRenaming.

(* The CPS transformation commutes with certain substitutions. More precisely,
   it commutes with a substitution [sigma] of values for variables, up to a
   transformation of the values in the codomain of [sigma].

   In the case of [cpsv], we have the following diagram: applying [sigma]
   first, followed with [cpsv], is the same as applying [cpsv] first, followed
   with [sigma >>> cpsv].

    cpsv v.[sigma] = (cpsv v).[sigma >>> cpsv]

  This can also be written in point-free style, that is, without mentioning
  the value [v]:

    subst sigma >>> cpsv = cpsv >>> subst (sigma >>> cpsv)

  As in the case of the renaming lemma (see CPSRenaming.v), this statement is
  proved by induction on the size of terms, together with an analogous
  statement about the function [cps]. *)

(* The proof depends on [CPSRenaming] via the lemmas [up_sigma_cpsv] and
   [upn_sigma_cpsv], which are declared as hints for [obvious]. *)

Lemma substitution:
  (
    forall v sigma sigma',
    sigma' = sigma >>> cpsv ->
    is_value_subst sigma ->
    (cpsv v).[sigma'] = cpsv v.[sigma]
  ) /\ (
    forall t c sigma c' sigma',
    sigma' = sigma >>> cpsv ->
    is_value_subst sigma ->
    substc sigma' c = c' ->
    (cps t c).[sigma'] = cps t.[sigma] c'
  ).
Proof.
  eapply mutual_induction.
  (* [cpsv] *)
  { intros n IHcps v Hvn sigma sigma' Heq Hsigma. subst.
    destruct v; asimpl; cpsv; asimpl; try reflexivity.
    (* Lam *)
    { erewrite IHcps by obvious. asimpl. reflexivity. }
  }
  (* [cps] *)
  { intros n IHcpsv IHcps t c Htn sigma c' sigma' Heq Hsigma Hsubstc. subst.
    value_or_app_or_let t; asimpl; cps.
    (* Case: [t] is a value. *)
    { erewrite apply_substitution by eauto.
      erewrite IHcpsv by obvious.
      reflexivity. }
    (* Case: [t] is an application. *)
    { eapply IHcps; obvious.
      simpl. f_equal.
      erewrite <- lift_up by tc.
      eapply IHcps; obvious.
      asimpl. do 2 f_equal.
      rewrite lift_reify.
      eapply reify_substitution.
      rewrite substc_substc.
      reflexivity. }
    (* Case: [t] is a [let] construct. *)
    { eapply IHcps; obvious.
      simpl.
      rewrite fold_up_up.
      do 2 f_equal.
      erewrite IHcps by first [ eapply substc_liftc_liftc; eauto | obvious ].
      autosubst. }
  }
Qed.

(* The projections of the above result. *)

Definition cpsv_substitution := proj1 substitution.
Definition cps_substitution  := proj2 substitution.

(* A point-free reformulation of the above result: [cpsv] commutes with an
   arbitrary substitution [sigma], up to a transformation of the values in the
   codomain of [sigma]. *)

Goal
  forall sigma,
  is_value_subst sigma ->
  cpsv >>> subst (sigma >>> cpsv) =
  subst sigma >>> cpsv.
Proof.
  intros. f_ext; intros v. asimpl. eauto using cpsv_substitution.
Qed.

(* This technical lemma is used below. *)

Lemma cpsv_cons:
  forall v,
  cpsv v .: ids = (v .: ids) >>> cpsv.
Proof.
  intros. f_ext; intros [|x]; autosubst.
Qed.

(* A corollary where the substitution [sigma] is [v .: ids], that is, a
   substitution of the value [v] for the variable 0. This one is about
   [cpsv]. *)

Lemma cpsv_substitution_0:
  forall v w,
  is_value v ->
  (cpsv w).[cpsv v/] =
  cpsv w.[v/].
Proof.
  intros. rewrite cpsv_cons. erewrite cpsv_substitution by obvious. reflexivity.
Qed.

(* Another corollary where the substitution [sigma] is [v .: ids], that is, a
   substitution of the value [v] for the variable 0. This one is about [cps]
   and concerns the case where the continuation is of the form [liftc 1 c], so
   it is unaffected. *)

Lemma cps_substitution_0:
  forall t c v,
  is_value v ->
  (cps t (liftc 1 c)).[cpsv v/] =
  cps t.[v/] c.
Proof.
  intros. eapply cps_substitution.
  { autosubst. }
  { obvious. }
  { eauto using substc_liftc_single. }
Qed.

(* A similar corollary where the substitution is [v .: w .: ids]. Here, the
   continuation is of the form [liftc 2 c], so is again unaffected. *)

Lemma cps_substitution_0_1:
  forall t c v w,
  is_value v ->
  is_value w ->
  (cps t (liftc 2 c)).[cpsv v, cpsv w/] =
  cps t.[v, w/] c.
Proof.
  intros. eapply cps_substitution.
  { autosubst. }
  { obvious. }
  { eauto using substc_liftc_double. }
Qed.

(* A corollary where the substitution [sigma] is [up (v .: ids)], that is, a
   substitution of the value [v] for the variable 1, and the continuation is
   the variable 0, so it is unaffected. *)

Lemma cps_substitution_1_O_Var_0:
  forall t v,
  is_value v ->
  (cps t (O (Var 0))).[up (cpsv v .: ids)] =
  cps t.[up (v .: ids)] (O (Var 0)).
Proof.
  intros. eapply cps_substitution.
  { rewrite cpsv_cons. obvious. }
  { obvious. }
  { reflexivity. }
Qed.

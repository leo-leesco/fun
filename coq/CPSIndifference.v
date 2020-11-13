Require Import MyTactics.
Require Import Sequences.
Require Import LambdaCalculusSyntax.
Require Import LambdaCalculusValues.
Require Import LambdaCalculusReduction.
Require Import CPSDefinition.

(* In a CPS term (i.e., a term produced by the CPS translation), the
   right-hand side of every application is a value, and the left-hand
   side of every [let] construct is a value. *)

Inductive is_cps : term -> Prop :=
| IsCPSVar:
    forall x,
    is_cps (Var x)
| IsCPSLam:
    forall t,
    is_cps t ->
    is_cps (Lam t)
| IsCPSApp:
    forall t1 t2,
    is_cps t1 ->
    is_cps t2 ->
    is_value t2 ->
    is_cps (App t1 t2)
| IsCPSLet:
    forall t1 t2,
    is_cps t1 ->
    is_cps t2 ->
    is_value t1 ->
    is_cps (Let t1 t2)
.

(* To prove that the above invariant holds, we must also define what it means
   for a continuation [c] to satisfy this invariant. *)

Inductive is_cps_continuation : continuation -> Prop :=
| IsCPSO:
    forall k,
    is_value k ->
    is_cps k ->
    is_cps_continuation (O k)
| IsCPSM:
    forall K,
    is_cps K ->
    is_cps_continuation (M K).

Local Hint Constructors is_cps is_cps_continuation : core.

(* [is_cps] is preserved by renamings. *)

Lemma is_cps_renaming:
  forall t,
  is_cps t ->
  forall sigma,
  is_ren sigma ->
  is_cps t.[sigma].
Proof.
  induction 1; intros sigma Hsigma; asimpl;
  try solve [ econstructor; obvious ].
  (* Var *)
  { destruct Hsigma as [ xi ? ]. subst sigma. asimpl. econstructor. }
Qed.

Local Hint Resolve is_cps_renaming : core.

Lemma is_cps_continuation_renaming:
  forall c i,
  is_cps_continuation c ->
  is_cps_continuation (liftc i c).
Proof.
  induction 1; simpl; econstructor; obvious.
Qed.

Local Hint Resolve is_cps_continuation_renaming : core.

(* [is_cps] is preserved by substitution. *)

Lemma is_cps_substitution_aux:
  forall sigma,
  (forall x, is_cps (sigma x)) ->
  (forall x, is_cps (up sigma x)).
Proof.
  intros sigma H [|x]; asimpl.
  { econstructor. }
  { eapply is_cps_renaming; obvious. }
Qed.

Lemma is_cps_substitution:
  forall K,
  is_cps K ->
  forall sigma,
  (forall x, is_cps (sigma x)) ->
  is_value_subst sigma ->
  is_cps K.[sigma].
Proof.
  induction 1; intros; asimpl; eauto;
  econstructor; eauto using is_cps_substitution_aux with obvious.
Qed.

Lemma is_cps_substitution_0:
  forall K v,
  is_cps K ->
  is_cps v ->
  is_value v ->
  is_cps K.[v/].
Proof.
  intros. eapply is_cps_substitution; obvious.
  intros [|x]; asimpl; eauto.
Qed.

(* Inversion lemmas for [is_cps]. *)

Lemma is_cps_Lam_inversion:
  forall t,
  is_cps (Lam t) ->
  is_cps t.
Proof.
  inversion 1; eauto.
Qed.

(* A CPS term reduces in the same manner in call-by-value and in call-by-name.
   Thus, the CPS transformation produces terms that are "indifferent" to which
   of these two reduction strategies is chosen. *)

Lemma cps_indifference_1:
  forall t1, is_cps t1 ->
  forall t2, cbv t1 t2 -> cbn t1 t2.
Proof.
  induction 1; intros; invert_cbv; obvious.
Qed.

Lemma cps_indifference_2:
  forall t1, is_cps t1 ->
  forall t2, cbn t1 t2 -> cbv t1 t2.
Proof.
  induction 1; intros; invert_cbn; obvious.
Qed.

(* [is_cps] is preserved by call-by-value and call-by-name reduction. *)

Lemma is_cps_cbv:
  forall t,
  is_cps t ->
  forall t',
  cbv t t' ->
  is_cps t'.
Proof.
  induction 1; intros; invert_cbv;
  eauto using is_cps, is_cps_substitution_0, is_cps_Lam_inversion.
Qed.

Lemma is_cps_cbn:
  forall t,
  is_cps t ->
  forall t',
  cbn t t' ->
  is_cps t'.
Proof.
  induction 1; intros; invert_cbn;
  eauto using is_cps, is_cps_substitution_0, is_cps_Lam_inversion.
Qed.

(* A CPS term reduces in the same manner in call-by-value and in call-by-name.
   The statement is here generalized to a sequence of reduction steps. *)

Lemma cps_star_indifference_1:
  forall t1 t2,
  star cbv t1 t2 ->
  is_cps t1 ->
  star cbn t1 t2.
Proof.
  induction 1; intros;
  eauto using cps_indifference_1, is_cps_cbv with sequences.
Qed.

Lemma cps_star_indifference_2:
  forall t1 t2,
  star cbn t1 t2 ->
  is_cps t1 ->
  star cbv t1 t2.
Proof.
  induction 1; intros;
  eauto using cps_indifference_2, is_cps_cbn with sequences.
Qed.

(* The main auxiliary lemmas. *)

Lemma is_cps_apply:
  forall c v,
  is_cps_continuation c ->
  is_cps v ->
  is_value v ->
  is_cps (apply c v).
Proof.
  inversion 1; intros; simpl; eauto using is_cps_substitution_0.
Qed.

Lemma is_cps_reify:
  forall c,
  is_cps_continuation c ->
  is_cps (reify c).
Proof.
  inversion 1; simpl; eauto.
Qed.

Lemma is_value_reify:
  forall c,
  is_cps_continuation c ->
  is_value (reify c).
Proof.
  inversion 1; simpl; eauto.
Qed.

Local Hint Resolve is_cps_apply is_cps_reify is_value_reify : core.

(* The main lemma. *)

Lemma cps_form:
(
  forall v,
  is_value v ->
  is_cps (cpsv v)
) /\ (
  forall t c,
  is_cps_continuation c ->
  is_cps (cps t c)
).
Proof.
  eapply mutual_induction.
  (* [cpsv] *)
  { intros n IHcps v Hvn ?.
    destruct v; [ | | false; obvious | false; obvious ].
    { cpsv; eauto. }
    { cpsv; eauto 6 with size. }
  }
  (* [cps] *)
  { intros n IHcpsv IHcps t c Htn Hc.
    value_or_app_or_let t; cps.
    (* Case: [t] is a value. *)
    { obvious. }
    (* Case: [t] is an application. *)
    { eapply IHcps; [ size | econstructor ].
      eapply IHcps; [ size | econstructor ].
      econstructor; obvious. }
    (* Case: [t] is a [let] construct. *)
    { eauto 8 with obvious. }
  }
Qed.

Lemma cps_form_main:
  forall t,
  is_cps (cpsinit t).
Proof.
  simpl. intros. eapply cps_form. unfold init. obvious.
Qed.

(* One property of CPS terms that we do not prove is that all applications are
   in tail position, or, in other words, that there is no need for reduction
   under a context. In fact, because a CPS-translated function expects two
   arguments, there *is* a need for reduction under a context, but only under
   a context of depth zero or one. *)

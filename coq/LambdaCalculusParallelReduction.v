Require Import Relations.
Require Import Sequences.
Require Import LambdaCalculusSyntax.
Require Import LambdaCalculusValues.
Require Import LambdaCalculusReduction.
Require Import MyTactics. (* TEMPORARY cannot be declared earlier; why? *)

(* -------------------------------------------------------------------------- *)

(* Parallel call-by-value reduction is stable by substitution. In fact,
   if [t1] parallel-reduces to [t2] and [sigma1] parallel-reduces to
   [sigma2], then [t1.[sigma1]] parallel-reduces to [t2.[sigma2]]. *)

Notation pcbv_subst sigma1 sigma2 :=
  (forall x, pcbv (sigma1 x) (sigma2 x)).

Lemma pcbv_subst_up:
  forall sigma1 sigma2,
  pcbv_subst sigma1 sigma2 ->
  pcbv_subst (up sigma1) (up sigma2).
Proof.
  intros ? ? ? [|x]; asimpl.
  { eapply red_refl; obvious. }
  { eapply red_subst; obvious. }
Qed.

Lemma pcbv_subst_cons:
  forall v1 v2 sigma1 sigma2,
  pcbv v1 v2 ->
  pcbv_subst sigma1 sigma2 ->
  pcbv_subst (v1 .: sigma1) (v2 .: sigma2).
Proof.
  intros ? ? ? ? ? ? [|x]; asimpl; eauto.
Qed.

Hint Resolve pcbv_subst_up pcbv_subst_cons : red obvious.

Lemma pcbv_parallel_subst:
  forall t1 t2,
  pcbv t1 t2 ->
  forall sigma1 sigma2,
  pcbv_subst sigma1 sigma2 ->
  is_value_subst sigma1 ->
  is_value_subst sigma2 ->
  pcbv t1.[sigma1] t2.[sigma2].
Proof.
  induction 1; try solve [ tauto ]; intros; subst.
  { rewrite subst_app, subst_lam.
    eapply RedParBetaV. obvious. obvious.
    { eapply IHred1; obvious. }
    { eapply IHred2; obvious. }
    autosubst. }
  { rewrite subst_let.
    eapply RedParLetV. obvious. obvious.
    { eapply IHred1; obvious. }
    { eapply IHred2; obvious. }
    autosubst. }
  { rewrite !subst_var. obvious. }
  { rewrite !subst_lam. eauto 6 with obvious. }
  { rewrite !subst_app. obvious. }
  { rewrite !subst_let. eauto 7 with obvious. }
Qed.

Hint Resolve pcbv_parallel_subst : red obvious.

(* -------------------------------------------------------------------------- *)

(* Parallel call-by-value reduction enjoys the diamond property. *)

(* The proof is by Takahashi's method (1995). We first define the function
   [fpbcv], for "full parallel call-by-value reduction". This function
   performs as much reduction as is possible in one step of [pcbv]. We prove
   that this is indeed the case: if [t1] reduces to [t2] by [pcbv], then [t2]
   reduces to [fpcbv t1]. The diamond property follows immediately. *)

Fixpoint fpcbv (t : term) : term :=
  match t with
  | Var x =>
      Var x
  | Lam t =>
      Lam (fpcbv t)
  | App (Lam t1) t2 =>
      if_value t2
        (fpcbv t1).[fpcbv t2/]
        (App (Lam (fpcbv t1)) (fpcbv t2))
  | App t1 t2 =>
      App (fpcbv t1) (fpcbv t2)
  | Let t1 t2 =>
      if_value t1
        (fpcbv t2).[fpcbv t1/]
        (Let (fpcbv t1) (fpcbv t2))
  end.

Ltac fpcbv :=
  simpl; if_value.

Lemma pcbv_takahashi:
  forall t1 t2,
  pcbv t1 t2 ->
  pcbv t2 (fpcbv t1).
Proof.
  induction 1; try solve [ tauto ]; subst;
  try solve [ fpcbv; eauto 9 with obvious ].
  (* RedAppLR *)
  { destruct t1; try solve [ fpcbv; obvious ].
    value_or_nonvalue u1; fpcbv; [ | obvious ].
    (* [t1] is a lambda-abstraction, and [u1] is a value. We have a redex. *)
    (* [pcbv (Lam _) t2] implies that [t2] is a lambda-abstraction, too. *)
    match goal with h: pcbv (Lam _) ?t2 |- _ => invert h end.
    (* Thus, the reduction of [t1] to [t2] is a reduction under lambda. *)
    simpl in IHred1. inversion IHred1; subst.
    (* The result is then... *)
    obvious. }
  (* RedLetLR *)
  { value_or_nonvalue t1; fpcbv; obvious. }
Qed.

Lemma diamond_pcbv:
  diamond pcbv.
Proof.
  intros t u1 ? u2 ?.
  exists (fpcbv t).
  split; eauto using pcbv_takahashi.
Qed.

Lemma diamond_star_pcbv:
  diamond (star pcbv).
Proof.
  eauto using diamond_pcbv, star_diamond.
Qed.

(* -------------------------------------------------------------------------- *)

(* Parallel reduction preserves the property of being stuck and the property
   of being irreducible. *)

Lemma pcbv_preserves_stuck:
  forall t1 t2,
  pcbv t1 t2 ->
  stuck t1 ->
  stuck t2.
Proof.
  induction 1; intros; subst; try solve [ tauto ].
  (* RedParBetaV *)
  { false. eapply stuck_irred; eauto 2 with obvious. }
  (* RedPatLetV *)
  { false. eapply stuck_irred; eauto 2 with obvious. }
  (* RedLam *)
  { inv stuck. }
  (* RedAppLR *)
  { inv stuck.
    { assert (forall t, t2 <> Lam t).
      { do 2 intro. subst.
        inv red; (* invert [pcbv _ (Lam _)] *)
        try solve [ false; eauto 2 with obvious | false; congruence ]. }
      eauto with stuck obvious. }
    { eauto with stuck. }
    { eauto with stuck obvious. }
  }
  (* RedLetLR *)
  { inv stuck.
    eauto with stuck. }
Qed.

Lemma pcbv_preserves_irred:
  forall t1 t2,
  pcbv t1 t2 ->
  irred cbv t1 ->
  irred cbv t2.
Proof.
  intros t1 t2 ?.
  rewrite !irred_cbv_characterization.
  intuition eauto 2 using pcbv_preserves_stuck with obvious.
Qed.

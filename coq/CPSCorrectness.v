Require Import MyTactics.
Require Import Sequences.
Require Import Relations.
Require Import LambdaCalculusSyntax.
Require Import LambdaCalculusValues.
Require Import LambdaCalculusReduction.
Require Import LambdaCalculusStandardization.
Require Import CPSDefinition.
Require Import CPSSpecialCases.
Require Import CPSSimulation.

(* [cbv+ . pcbv] implies [pcbv*]. *)

Lemma technical_inclusion_0:
  inclusion plus_cbv_pcbv (star pcbv).
Proof.
  intros t1 t2. unfold composition. intros. unpack.
  eauto 6 using cbv_subset_pcbv, plus_covariant with sequences.
Qed.

(* [(cbv+ . pcbv)*] implies [pcbv*]. *)

Lemma technical_inclusion_1:
  inclusion (star plus_cbv_pcbv) (star pcbv).
Proof.
  eapply inclusion_transitive; [| eapply inclusion_star_star ].
  eapply star_covariant_inclusion.
  eapply technical_inclusion_0.
Qed.

(* A simplified simulation diagram. *)

Lemma simulation_cbv_pcbv:
  forall t t',
  star cbv t t' ->
  star pcbv (cps t init) (cps t' init).
Proof.
  intros t t' Hred.
  (* According to the simulation diagram (iterated), [cps t c] reduces to
     [cps v c] via a series of [cbv] and [pcbv] steps. *)
  destruct (star_diamond_left _ _ _ cps_init_simulation _ _ Hred _ eq_refl)
    as (?&?&?). subst.
  (* Thus, [cps t c] reduces to [cps t' c] via [pcbv*]. *)
  eapply technical_inclusion_1. eauto.
Qed.

(* If [t] diverges, then [cps t init] diverges, too. *)

Lemma cps_preserves_divergence:
  forall t,
  infseq cbv t ->
  infseq cbv (cps t init).
Proof.
  intros.
  eapply pcbv_preserves_divergence.
  eapply infseq_simulation.
  { eapply cps_init_simulation. }
  { eauto. }
  { tauto. }
Qed.

(* If [t] converges to a value [v], then [cps t init] converges to a value [w].
   Furthermore, [w] reduces to [cpsv v] via a number of parallel reduction
   steps. *)

Lemma cps_preserves_convergence:
  forall t v,
  star cbv t v ->
  is_value v ->
  exists w,
  star cbv (cps t init) w /\
  is_value w /\
  star pcbv w (cpsv v).
Proof.
  intros ? ? Htv Hv.
  (* [cps t init] reduces to [cps v init] via [pcbv*]. *)
  generalize (simulation_cbv_pcbv _ _ Htv); intro Hred.
  (* [cps v init] is [cpsv v]. *)
  assert (Heq: cps v init = cpsv v).
  { cps. reflexivity. }
  (* Thus, [cps t init] reduces to [cpsv v] via [pcbv*]. *)
  rewrite Heq in Hred.
  (* Bifurcate this reduction sequence. *)
  forward1 crarys_lemma9. clear Hred.
  (* This gives us the value [w] that we are looking for. *)
  eexists. split. eauto. split.
  { eauto using
      (star_implication_reversed _ ipcbv_preserves_values_reversed)
      with obvious. }
  { eauto using star_covariant, ipcbv_subset_pcbv. }
Qed.

(* If [t] is stuck, then [cps t c] is stuck. Not a really interesting
   property, but we prove it, just so that no stone is left unturned. *)

Lemma cps_preserves_stuck:
  forall t,
  stuck t ->
  forall c,
  stuck (cps t c).
Proof.
  induction 1; intros.
  (* StuckApp *)
  { rewrite cps_app_value_value by eauto.
    eapply StuckAppL.
    eapply StuckApp; [ obvious | obvious |].
    (* Only [Lam] is translated to [Lam]. *)
    intros. destruct v1.
    { cpsv. congruence. }
    { cpsv. false. congruence. }
    { obvious. }
    { obvious. }
  }
  (* StuckAppL *)
  { cps. eauto. }
  (* StuckAppR *)
  { rewrite cps_app_value by eauto. eauto. }
  (* StuckLetL *)
  { cps. eauto. }
Qed.

(* As a corollary, the property of going wrong is preserved by the CPS
   transformation. *)

Lemma cps_preserves_going_wrong:
  forall t,
  goes_wrong t ->
  goes_wrong (cps t init).
Proof.
  intros ? [ t' [ Htt' ? ]].
  (* [cps t init] reduces to [cps t' init] via [pcbv*]. *)
  generalize (simulation_cbv_pcbv _ _ Htt'); intro Hred.
  (* Bifurcate this reduction sequence. *)
  forward1 crarys_lemma9. clear Hred.
  (* This gives us the stuck term we are looking for. *)
  eexists. split. eauto.
  eauto using cps_preserves_stuck, reverse_star_ipcbv_preserves_stuck.
Qed.

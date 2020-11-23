Require Import MyTactics.
Require Import Sequences.
Require Import Relations.
Require Import LambdaCalculusSyntax.
Require Import LambdaCalculusValues.
Require Import LambdaCalculusReduction.
Require Import CPSDefinition.
Require Import CPSContextSubstitution.
Require Import CPSRenaming.
Require Import CPSSubstitution.
Require Import CPSKubstitution.
Require Import CPSSpecialCases.

(* We now prepare for the statement of the "magic step" lemma [pcbv_cps]. This
   lemma states that if the continuations [c1] and [c2] are similar, then [cps
   t c1] is able to reduce via [pcbv] to [cps t c2]. We use parallel reduction
   [pcbv] because we must allow reduction to take place under [Lam] and in the
   right-hand side of [Let]. We do not need the full power of [pcbv]: we only
   reduce zero or one redexes, never more. *)

(* A simplified copy of this file, where we pretend that the [Let] construct
   does not exist, can be found in [CPSSimulationWithoutLet.v]. There, there
   is no need for parallel reduction; a simpler simulation diagram holds. *)

(* Similarity of continuations is defined as follows: *)

Inductive similar : continuation -> continuation -> Prop :=
| SimilarReify:
    forall c,
    similar (O (reify c)) c
| SimilarM:
    forall K1 K2,
    pcbv K1 K2 ->
    similar (M K1) (M K2).

(* Similarity is preserved by lifting. *)

Lemma similar_liftc_liftc:
  forall i c1 c2,
  similar c1 c2 ->
  similar (liftc i c1) (liftc i c2).
Proof.
  induction 1; intros; simpl.
  { rewrite lift_reify. econstructor. }
  { econstructor. eapply red_subst; obvious. }
Qed.

(* The lemmas [pcbv_apply] and [pcbv_reify] are preliminaries for the
   "magic step" lemma. *)

Lemma pcbv_apply:
  forall c1 c2,
  similar c1 c2 ->
  forall v,
  pcbv (apply c1 (cpsv v)) (apply c2 (cpsv v)).
Proof.
  inversion 1; subst; intros; [ destruct c2 |]; simpl.
  (* Case: both [c1] and [c2] are an object-level continuation [k].
     No computation step is taken. *)
  { eapply red_refl; obvious. }
  (* Case: [c1] is a two-level eta-expansion of [c2], which is a
     meta-level continuation [K]. One beta-reduction step is taken. *)
  { eapply pcbv_RedBetaV; obvious. }
  (* Case: [c1] and [c2] are similar meta-level continuations. The
     required reduction steps are provided directly by the similarity
     hypothesis. *)
  { eapply red_subst; obvious. }
Qed.

Lemma pcbv_reify:
  forall c1 c2,
  similar c1 c2 ->
  pcbv (reify c1) (reify c2).
Proof.
  inversion 1; subst; intros; [ destruct c2 |]; simpl.
  (* Case: both [c1] and [c2] are an object-level continuation [k].
     No computation step is taken. *)
  { eapply red_refl; obvious. }
  (* Case: [c1] is a two-level eta-expansion of [c2], which is a
     meta-level continuation [K]. No computation step is taken. *)
  { eapply red_refl; obvious. }
  (* Case: [c1] and [c2] are similar meta-level continuations. The
     required reduction steps are provided directly by the similarity
     hypothesis, applied under a lambda-abstraction. *)
  { eapply RedLam; obvious. }
  (* We could arrange to just write [obvious] in each of the above
     cases and finish the entire proof in one line, but we prefer to
     explicitly show what happens in each case. *)
Qed.

Local Hint Resolve red_refl : obvious.

(* The "magic step" lemma. *)

Lemma pcbv_cps:
  forall t c1 c2,
  similar c1 c2 ->
  pcbv (cps t c1) (cps t c2).
Proof.
  (* The proof is by induction on the size of [t]. *)
  size_induction t. intros c1 c2 Hsimilar.
  value_or_app_or_let t; cps.
  (* Case: [t] is a value. *)
  { eauto using pcbv_apply. }
  (* Case: [t] is an application. *)
  { eapply IH; [ size | econstructor ].
    eapply IH; [ size | econstructor ].
    eapply RedAppLR; obvious.
    eapply red_subst; obvious.
    eauto using pcbv_reify. }
  (* Case: [t] is a [let] construct. *)
  { eapply IH; [ size | econstructor ].
    eapply RedLetLR; obvious.
    eapply IH; [ size |].
    eauto using similar_liftc_liftc. }
Qed.

(* The small-step simulation theorem: if [t1] reduces to [t2], then [cps t1 c]
   reduces to [cps t2 c] via at least one step of [cbv], followed with one
   step of [pcbv]. *)

(* Although the reduction strategies [cbv] and [pcbv] allow reduction in the
   left-hand side of applications, at an arbitrary depth, in reality the CPS
   transformation exploits this only at depth 0 or 1. We do not formally
   establish this result (but could, if desired). *)

Notation plus_cbv_pcbv :=
  (composition (plus cbv) pcbv).

Lemma cps_simulation:
  forall t1 t2,
  cbv t1 t2 ->
  forall c,
  is_value (reify c) ->
  plus_cbv_pcbv
    (cps t1 c)
    (cps t2 c).
Proof.
  induction 1; intros; subst; try solve [ tauto ].
  (* Beta-reduction. *)
  { rewrite cps_app_value_value by eauto. cpsv.
    (* We are looking at two beda redexes. Perform exactly two steps of [cbv]. *)
    eexists. split; [ eapply plus_left; [ obvious | eapply star_step; [ obvious | eapply star_refl ]] |].
    (* There remains one step of [pcbv]. *)
    rewrite cps_substitution_1_O_Var_0 by eauto.
    rewrite lift_up by tc.
    rewrite cps_kubstitution_0. asimpl.
    eapply pcbv_cps. econstructor.
  }
  (* Let *)
  { rewrite cps_let_value by eauto.
    (* We are looking at a let-redex. Perform exactly one step of [cbv]. *)
    eexists. split; [ eapply plus_left; [ obvious | eapply star_refl ] |].
    (* There remains a trivial (reflexive) step of [pcbv]. *)
    rewrite cps_substitution_0 by eauto.
    eapply red_refl; obvious.
  }
  (* Reduction in the left-hand side of an application. *)
  { cps. eapply IHred. eauto. }
  (* Reduction in the right-hand side of an application. *)
  { rewrite !cps_app_value by eauto. eapply IHred. tauto. }
  (* Reduction in the left-hand side of [Let]. *)
  { cps. eapply IHred. tauto. }
Qed.

(* We now specialize the above result to the identity continuation and
   state it as a commutative diagram. *)

Lemma cps_init_simulation:
  let sim t t' := (cps t init = t') in
  diamond22
    cbv sim
    plus_cbv_pcbv sim.
Proof.
  assert (is_value (reify init)). { simpl. eauto. }
  unfold diamond22. intros. subst. eauto using cps_simulation.
Qed.

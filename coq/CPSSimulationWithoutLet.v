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

(* This file is a simplified copy of [CPSSimulation]. Here, we consider how
   the proof of the simulation lemma is simplified in the absence of a [Let]
   construct. We simply pretend that this construct does not exist, and skip
   the proof cases where it appears. *)

(* -------------------------------------------------------------------------- *)

(* The definition of similarity of continuations boils down to just one rule:
   [O (reify c)] is similar to [c]. *)

Inductive similar : continuation -> continuation -> Prop :=
| SimilarReify:
    forall c,
    similar (O (reify c)) c.

(* -------------------------------------------------------------------------- *)

(* The lemma [pcbv_apply] is simplified: its conclusion uses [star cbv] instead
   of [pcbv]. In fact, zero or one step of reduction is needed. *)

Lemma pcbv_apply:
  forall c1 c2,
  similar c1 c2 ->
  forall v,
  star cbv (apply c1 (cpsv v)) (apply c2 (cpsv v)).
Proof.
  inversion 1; subst; intros; destruct c2; simpl.
  (* Case: both [c1] and [c2] are an object-level continuation [k].
     No computation step is taken. *)
  { eauto with sequences. }
  (* Case: [c1] is a two-level eta-expansion of [c2], which is a
     meta-level continuation [K]. One beta-reduction step is taken. *)
  { eauto with sequences obvious. }
Qed.

(* The lemma [pcbv_reify] is simplified: its conclusion becomes an equality. *)

Lemma pcbv_reify:
  forall c1 c2,
  similar c1 c2 ->
  reify c1 = reify c2.
Proof.
  inversion 1; subst; intros; destruct c2; simpl; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* The "magic step" lemma is simplified: its conclusion uses [star cbv] instead
   of [pcbv]. In fact, zero or one step of reduction is needed. The magic lies
   in the case of applications, where [pcbv_reify] is used. *)

Lemma pcbv_cps:
  forall t c1 c2,
  similar c1 c2 ->
  star cbv (cps t c1) (cps t c2).
Proof.
  (* The proof does NOT require an induction. *)
  intros t c1 c2 Hsimilar.
  value_or_app_or_let t; cps.
  (* Case: [t] is a value. *)
  { eauto using pcbv_apply. }
  (* It turns out by magic that this proof case is trivial: it suffices to
     take zero reduction steps. (That took me an evening to find out.) Thus,
     no induction hypothesis is needed! *)
  { erewrite pcbv_reify by eauto.
    eauto with sequences. }
  (* Case: [t] is a [let] construct. We pretend this case is not there. *)
  { admit. }
Admitted. (* normal *)

(* -------------------------------------------------------------------------- *)

(* The small-step simulation theorem: if [t1] reduces to [t2], then [cps t1 c]
   reduces to [cps t2 c] via at least one step of [cbv]. (In fact, two or three
   steps are required.) *)

Lemma cps_simulation:
  forall t1 t2,
  cbv t1 t2 ->
  forall c,
  is_value (reify c) ->
  plus cbv
    (cps t1 c)
    (cps t2 c).
Proof.
  induction 1; intros; subst; try solve [ tauto ].
  (* Beta-reduction. *)
  { rewrite cps_app_value_value by eauto. cpsv.
    (* We are looking at two beda redexes. Perform exactly two steps of [cbv]. *)
    eapply plus_left. obvious.
    eapply star_step. obvious.
    (* Push the inner substitution (the actual argument) into [cps]. *)
    rewrite cps_substitution_1_O_Var_0 by eauto.
    rewrite lift_up by tc.
    (* Push the outer substitution (the continuation) into [cps]. *)
    rewrite cps_kubstitution_0.
    asimpl.
    (* Conclude. *)
    eapply pcbv_cps. econstructor.
  }
  (* Let. We pretend this case is not there. *)
  { admit. }
  (* Reduction in the left-hand side of an application. *)
  { cps. eapply IHred. eauto. }
  (* Reduction in the right-hand side of an application. *)
  { rewrite !cps_app_value by eauto. eapply IHred. tauto. }
  (* Reduction in the left-hand side of [Let]. We pretend this case is not there. *)
  { admit. }
Admitted. (* normal *)

(* -------------------------------------------------------------------------- *)

(* We now specialize the above result to the identity continuation and
   state it as a commutative diagram. *)

Lemma cps_init_simulation:
  let sim t t' := (cps t init = t') in
  diamond22
    cbv sim
    (plus cbv) sim.
Proof.
  assert (is_value (reify init)). { simpl. eauto. }
  unfold diamond22. intros. subst. eauto using cps_simulation.
Qed.

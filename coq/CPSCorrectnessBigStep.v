Require Import MyTactics.
Require Import Sequences.
Require Import LambdaCalculusSyntax.
Require Import LambdaCalculusValues.
Require Import LambdaCalculusReduction.
Require Import LambdaCalculusBigStep.
Require Import CPSDefinition.
Require Import CPSSubstitution.
Require Import CPSKubstitution.

(* In this file, we prove that the CPS transformation is semantics-preserving,
   that is, if the source term [t] produces the source value [v], then the
   transformed term [cpsinit t] produces the transformed value [cpsv v]. *)

(* This proof, based on a big-step semantics, is relatively straightforward.
   Compared with the small-step approach in CPSSimulation, it requires the
   same fundamental lemmas about renaming and substitution, but is simpler, as
   it does not involve the notions of "similar" continuations or parallel
   call-by-value reduction. *)

(* This statement, however, is a bit weaker, in that it does not guarantee
   that a diverging program is transformed into a diverging program. To do
   so, we would have to define a divergence predicate in big-step style,
   and prove that divergence is preserved. *)

(* -------------------------------------------------------------------------- *)

(* The term [App (reify c) v] reduces (in zero or one steps) to [apply c v]. *)

Lemma star_cbv_App_reify:
  forall c v,
  is_value v ->
  star cbv (App (reify c) v) (apply c v).
Proof.
  (* By cases on the continuation [c]. *)
  intros. destruct c; unfold reify, apply.
  (* For an object-level continuation, this is trivial. *)
  { finished. obvious. }
  (* For a meta-level continuation, one beta-reduction step is needed. *)
  { step. finished. obvious. }
Qed.

(* -------------------------------------------------------------------------- *)

(* The main lemma. If the term [t] produces the value [v], then, for an
   arbitrary continuation [c], the term [cps t c] simulates (behaves like)
   the term [apply c (cpsv v)]. This formalizes the intuitive idea that a
   CPS-transformed term passes its final result to its continuation. *)

Lemma cps_correctness_inductive:
  forall t v,
  bigcbv t v ->
  forall c,
  is_value (reify c) ->
  sim (cps t c) (apply c (cpsv v)).

(* A local tactic to apply and forget an induction hypothesis. *)
Local Ltac exploit IH :=
  eapply transitive_sim; [
    eapply IH; obvious
  | clear IH; simpl apply; try eapply reflexive_sim
  ].
(* A local tactic to perform one step of call-by-value reduction. *)
Local Ltac cbv_sim :=
  eapply transitive_sim; [ eapply cbv_sim; obvious | ].

Proof.
  (* The proof is by induction on the derivation of [bigcbv t v]. *)
  induction 1; intros; cps.

  (* Case: [BigcbvValue]. Immediate. *)
  { apply reflexive_sim. }

  (* Case: [BigcbvApp]. We have three induction hypotheses, which (once
     suitably instantiated) give us three [sim]ulation assertions. Since
     [sim] is a transitive relation, we can use them one after the other.
     A few technical lemmas are required in order to push substitutions
     into [cps], but the proof is otherwise straightforward. *)
  {
    (* Exploit the first induction hypothesis. *)
    exploit IHbigcbv1.
    (* We have a substitution that applies only to the continuation, not
       to the term [t2]. Simplify. *)
    rewrite cps_kubstitution_0.
    (* Exploit the second induction hypothesis. *)
    exploit IHbigcbv2. asimpl.
    (* Unfold the definition of [cpsv (Lam u1)]. *)
    cpsv.
    (* We have two beta-redexes. Reduce them. *)
    cbv_sim.
    cbv_sim.
    (* Typing [asimpl] here helps read the goal, but does not actually
       simplify the proof. Better keep the two substitutions separate,
       so we can push them into [cps] one at a time. *)
    (* The first substitution concerns only the term, not the continuation. *)
    rewrite cps_substitution_1_O_Var_0 by obvious.
    rewrite lift_up by tc.
    (* The second substitution concerns only the continuation, not the term. *)
    rewrite cps_kubstitution_0. unfold substc. asimpl.
    (* Exploit the third induction hypothesis. *)
    exploit IHbigcbv3.
    (* The result now follows from the previous little lemma. *)
    eauto using star_cbv_sim, star_cbv_App_reify with is_value.
  }

  (* Case: [BigcbvLet]. *)
  {
    (* Exploit the first induction hypothesis. *)
    exploit IHbigcbv1.
    (* Reduce a [let]-redex. *)
    cbv_sim. asimpl.
    (* We have a substitution of [cpsv v1] for variable 0
       and of an irrelevant value for variable 1. Simplify. *)
    erewrite cps_substitution_0_1 by obvious. asimpl.
    (* Exploit the second induction hypothesis. *)
    exploit IHbigcbv2.
  }

Qed.

(* -------------------------------------------------------------------------- *)

(* As an immediate consequence of the main lemma above, we get the semantic
   preservation theorem that was announced at the beginning of this file. *)

(* Whereas [sim] was used (for convenience) in the statement of the main lemma,
   this theorem is stated directly in terms of [bigcbv]. *)

Theorem cps_correctness:
  forall t v,
  bigcbv t v ->
  bigcbv (cpsinit t) (cpsv v).
Proof.
  intros.
  eapply cps_correctness_inductive.
  { eauto. }
  { unfold init, reify. obvious. }
  { unfold init, apply. asimpl. eauto with bigcbv is_value. }
Qed.

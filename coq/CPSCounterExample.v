Require Import MyTactics.
Require Import Sequences.
Require Import LambdaCalculusSyntax.
Require Import LambdaCalculusValues.
Require Import LambdaCalculusReduction.
Require Import CPSDefinition.

(* The single-step simulation lemma in Danvy and Filinski's paper states that
   if [t1] reduces to [t2], then [cps t1 c] reduces (in one or more steps) to
   [cps t2 c]. Although this lemma is true in the pure lambda calculus, it
   fails when the calculus is extended with [Let]. This file provides two
   counter-examples. *)

(* Although Danvy and Filinski's paper does not claim that this lemma holds
   when the calculus is extended with [Let], it does not indicate that the
   lemma fails, either. *)

(* -------------------------------------------------------------------------- *)

(* The tactic [analyze] assumes that there is a hypothesis [star cbv t1 t2].
   It checks that [t1] and [t2] are distinct and, if [t1] reduces to [t'1],
   updates this hypothesis to [star cbv t'1 t2]. Repeating this tactic allows
   proving that [t1] does *not* reduce to [t2]. *)

Ltac analyze :=
  invert_star_cbv; repeat invert_cbv; compute in *; fold cbv_mask in *;
  repeat match goal with h: True |- _ => clear h end.

Transparent cps cpsv. (* required by [compute] *)

(* -------------------------------------------------------------------------- *)

(* Consider the term [t1], defined as follows. In informal syntax, [t1]
   is written (\z.let w = z in w) (\x.x). *)

Definition t1 :=
  App (Lam (Let (Var 0) (Var 0))) (Lam (Var 0)).

(* The term [t1] reduces to [t2], which in informal syntax is written
   let w = \x.x in w. *)

Definition t2 :=
  Let (Lam (Var 0)) (Var 0).

Goal
  cbv t1 t2.
Proof.
  unfold t1, t2. obvious.
Qed.

(* The single-step simulation diagram is violated: [cps t1 init] does
   *not* reduce (in any number of steps) to [cps t2 init]. *)

Goal
  ~ (star cbv (cps t1 init) (cps t2 init)).
Proof.
  compute; fold cbv_mask. intro.
  analyze.
  analyze.
  (* This point is the near miss:
     [cps t1 init] has now reduced to a [Let] construct, whereas
     [cps t2 init] is a similar-looking [Let] construct.
     Both have the same value on the left-hand side of the [Let].
     But the right-hand sides of the [Let] construct differ. *)
  analyze.
  analyze.
  analyze.
Qed.

(* Let us summarize.

   The term [t1] reduces in one step to [t2] as follows:

     (\z.let w = z in w) (\x.x)
     ->
     let w = \x.x in w

   The term [cps t1 init], in informal notation, is as follows:

     (\z.\k.let w = z in k w)
     (\x.\k. k x)
     (\w.w)

   This term reduces in two steps to:

     let w = \x.\k. k x in
     (\w.w) w

   But the term [cps t2 init], in informal notation, is:

     let w = \x.\k. k x in
     w

   This is our near miss. Both terms are [let] constructs and both have
   the same left-hand side, but the right-hand sides differ by a beta-v
   reduction. Thus, [cps t1 init] does not reduce *in call-by-value* to
   [cps t2 init]. In order to allow [cps u1 init] to join [cps u2 init],
   we must allow beta-v reductions in the right-hand side of [let]
   constructs (and, it turns out, under lambda-abstractions, too.)
   This is visible in the proof of the [simulation] lemma in the file
   CPSSimulation: there, we use the reduction strategy [pcbv], which
   allows (parallel) beta-v reductions under arbitrary contexts. *)

(* This counter-example is one of two closed counter-examples of minimal size.
   It has size 4 (counting [Lam], [App], and [Let] nodes) and involves only
   one [Let] construct. There are no smaller counter-examples. An exhaustive
   search procedure, coded in OCaml, was used to find it. *)

Require Import MyTactics.
Require Import LambdaCalculusSyntax.
Require Import LambdaCalculusValues.
Require Import LambdaCalculusReduction.
Require Import STLCDefinition.
Require Import STLCLemmas.

(* -------------------------------------------------------------------------- *)

(*|

The progress theorem: a closed, well-typed term must either be able to
make one step of reduction or be a value.

|*)

Lemma jt_progress:
  forall Gamma t T,
  jt Gamma t T ->
  closed t ->
  (exists t', cbv t t') \/ is_value t.
Ltac use_ih ih :=
  destruct ih; [ eauto with closed | unpack; eauto with red |  ].
Proof.
Abort.

(* -------------------------------------------------------------------------- *)

(*|

The following inversion lemma is needed in the proof of progress (above).

If a closed value admits a function type `TyFun T1 T2`, then this value
must be a lambda-abstraction.

|*)

Lemma invert_jt_TyFun:
  forall Gamma t T1 T2,
  jt Gamma t (TyFun T1 T2) ->
  closed t ->
  is_value t ->
  exists t', t = Lam t'.
Proof.
Abort.

(* -------------------------------------------------------------------------- *)

(*|

The subject reduction theorem, also known as type preservation: the typing
judgement is preserved by one step of reduction.

This is proved here for `cbv`, but could be proved for other notions of
reduction, such as `cbn`, or strong reduction.

|*)

Lemma jt_preservation:
  forall Gamma t T,
  jt Gamma t T ->
  forall t',
  cbv t t' ->
  jt Gamma t' T.
Proof.
Abort.

(* -------------------------------------------------------------------------- *)

(*|

The following substitution lemma is needed in the proof of subject
reduction (above).

A direct attempt to prove this lemma by induction fails (see below).

A better approach is to state a more general substitution lemma and obtain
this lemma as a special case: see STLCLemmas.v.

|*)

Lemma jt_te_substitution_0:
  forall Delta t1 U,
  jt Delta t1 U ->
  forall Gamma t2 T,
  Delta = T .: Gamma ->
  jt Gamma t2 T ->
  jt Gamma t1.[t2/] U.
Proof.
  (* Let us attempt to naively prove this statement by induction. *)
  induction 1; intros; subst; asimpl.
  all: swap 2 3. (* deal with JTApp before JTLam *)
  (* JTVar. *)
  { (* By cases on the variable `x`. Either it is zero, or nonzero. *)
    destruct x as [|x].
    { asimpl. eauto. }
    { asimpl. eauto with jt. } }
  (* JTApp. *)
  (* This case just works, thanks to the induction hypotheses. *)
  { eauto with jt. }
  (* JTLam. *)
  { (* We must typecheck a lambda, so we must apply JTLam. *)
    eapply JTLam.
    (* We would now like to apply the induction hypothesis, but this
       fails, because the statement of the lemma allows substituting a
       term for variable 0, but we are now attempting to substitute a
       term for variable 1. *)
    Fail eapply IHjt.
    (* The moral of the story is that it is preferable to state a lemma
       that allows applying an arbitrary substitution (of terms for
       term variables) to a term. This will give rise to statements
       that are more general, therefore both more powerful and easier
       to read. See STLCLemmas. *)
Abort.

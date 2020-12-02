Require Import MyTactics.
Require Import Sequences.
Require Import LambdaCalculusSyntax.
Require Import LambdaCalculusValues.
Require Import LambdaCalculusReduction.
Require Import SystemFDefinition.
Require Import SystemFLemmas.

(*|

-------
Prelude
-------

We begin with a direct attempt to establish type preservation (that is,
subject reduction) for System F, and find that we need a key inversion
lemma first.

|*)

Goal (* jf_preservation *)
  forall Gamma t T,
  jf Gamma t T ->
  forall t',
  cbv t t' ->
  jf Gamma t' T.
Proof.
Abort.

(*|

----------------------------------
An inversion lemma (first attempt)
----------------------------------

|*)

(*|

We wish to establish an inversion lemma for the typing rule for
lambda-abstractions.

A first version of the statement is as follows: if under `Gamma` a
lambda-abstraction `Lam t` has type `TyFun T U`, then under the extended
environment `T .: Gamma`, the term `t` must have type `U`. Let us try to prove
this:

|*)

Goal (* invert_jf_Lam_TyFun *)
  forall Gamma t' T' ,
  jf Gamma t' T' ->
  forall t T U,
  t' = Lam t ->
  T' = TyFun T U ->
  jf (T .: Gamma) t U.
Proof.
Abort.

(*|

-----------------------------------
An inversion lemma (second attempt)
-----------------------------------

|*)

(*|

The previous attempt fails, because the statement is not general enough. We
cannot restrict our attention to the situation where the term `Lam t` has a
function type. We must also reason about the situations where it has a
polymorphic type that can be instantiated to a function type.

Thus, we propose a more general statement, where `Lam t` has type `T'` and
`T'` can be weakened (via a subsumption relation) to `TyFun T U`.

This relation is defined by just one rule: the type `TyAll T` is a subtype of
the type `T.[U/]`. When necessary, we will use the reflexive transitive
closure of this relation, [star sub], so as to allow for a sequence of
subtyping steps.

|*)

Inductive sub : ty -> ty -> Prop :=
| Sub:
    forall T T' U,
    T' = T.[U/] ->
    sub (TyAll T) T'.

(*|

Here is a second attempt at the inversion lemma for lambda-abstractions.
Instead of requiring an equality between `T'` and `TyFun T U`, we allow
a sequence of subsumption steps. Thus, this statement is stronger.

|*)

Goal (* invert_jf_Lam_TyFun *)
  forall Gamma t' T' ,
  jf Gamma t' T' ->
  forall t T U,
  t' = Lam t ->
  star sub T' (TyFun T U) ->
  jf (T .: Gamma) t U.
Proof.
Abort.

(*|

----------------------------------
An inversion lemma (final attempt)
----------------------------------

|*)

(*|

If we had an explicit syntax for type abstractions and type applications,
we would see that what we are doing in the previous proof attempt is to
reduce a type redex (that is, a type application of a type abstraction).
The difficulty that we are hitting is to prove that this process must
terminate.

The intuitive reason why it must terminate is that a type derivation for
the term `Lam t` must end with a *finite* number of uses of the typing
rules `JFTyAbs` and `JFTyApp`, and our proof peels them away one by one.
Crucially, we must argue that our use of the type substitution lemma
`jf_ty_substitution_0` *preserves* the structure of the derivation, so
does not increase the number of uses of `JFTyAbs` and `JFTyApp`.

To do this, we introduce an auxiliary typing judgment, `jtn`. (See
SystemFLemmas.) This judgement is parameterized with an integer `n` that
counts the number of uses of `JFTyAbs` and `JFTyApp` at the root of a type
derivation. This allows us to prove the lemma `invert_jtn_Lam_TyFun` by
induction on `n`.

We show that the judgements `jtn` and `jf` are equivalent, that is, `jf`
can be viewed as a version of `jtn` where the parameter `n` is ignored.
(See SystemFLemmas.) Thus, we can reason in terms of `jtn` where
necessary, and use the simpler judgement `jf` elsewhere.

|*)

Lemma invert_jtn_Lam_TyFun:
  forall n Gamma t T' T U,
  jtn n Gamma (Lam t) T' ->
  star sub T' (TyFun T U) ->
  jt (T .: Gamma) t U.
Proof.
Admitted.

(*|

The inversion lemma can be reformulated in terms of `jf`.

|*)

Lemma invert_jf_Lam_TyFun:
  forall Gamma t T U,
  jf Gamma (Lam t) (TyFun T U) ->
  jf (T .: Gamma) t U.
Proof.
  intros.
  forward jf_jt. unfold jt in *. unpack.
  forward invert_jtn_Lam_TyFun. { eauto with sequences. }
  eauto using jt_jf.
Qed.

(*|
-----------------
Type preservation
-----------------
|*)

(*|

The typing judgement is preserved by one step of reduction.

|*)

Lemma jf_preservation:
  forall Gamma t T,
  jf Gamma t T ->
  forall t',
  cbv t t' ->
  jf Gamma t' T.
Proof.
  (* By induction on the type derivation. *)
  induction 1; intros; subst; try solve [ invert_cbv ].
Abort.

(*|
--------
Progress
--------
|*)

(*|

An inversion lemma: if a closed value admits a function type `TyFun T1 T2`,
then it must be a lambda-abstraction.

|*)

Lemma invert_jtn_TyFun:
  forall n Gamma t T,
  jtn n Gamma t T ->
  forall T1 T2,
  star sub T (TyFun T1 T2) ->
  closed t ->
  is_value t ->
  exists t', t = Lam t'.
Proof.
  (* We do not comment this proof in detail. It is analogous in its
     general structure to the proof of `invert_jtn_Lam_TyFun`. *)
  induction n; inversion 1; intros; subst;
  try solve [ false; eauto with closed ].

  (* Case: JTNLam. *)
  { eauto. }

  (* Case: JTNTyAbs. *)
  { pick star invert. pick sub invert.
    eapply IHn; [ | eauto | eauto | eauto ].
    eauto using jtn_ty_substitution_0. }

  (* Case: JTNTyApp. *)
  { eauto using sub with sequences. }
Qed.

Lemma invert_jf_TyFun:
  forall Gamma t T1 T2,
  jf Gamma t (TyFun T1 T2) ->
  closed t ->
  is_value t ->
  exists t', t = Lam t'.
Proof.
  intros.
  forward jf_jt. unfold jt in *. unpack.
  forward invert_jtn_TyFun. { eauto with sequences. }
  eauto using jt_jf.
Qed.

(*|

The progress theorem: a closed, well-typed term
must either be able to make one step of reduction
or be a value.

|*)

Lemma jf_progress:
  forall Gamma t T,
  jf Gamma t T ->
  closed t ->
  (exists t', cbv t t') \/ is_value t.
Ltac use_ih ih :=
  destruct ih; [ eauto with closed | unpack; eauto with red |  ].
Proof.
  (* By induction on the type derivation. *)
  induction 1; intros; subst.
  (* Case: JFVar. *)
  { false. eauto with closed. }
  (* Case: JFLam. *)
  { obvious. }
  (* Case: JFApp. *)
  { use_ih IHjf1.
    (* Reason in the same way about `t2`. *)
    use_ih IHjf2.
    (* We wish to prove that `App t1 t2` is a beta-redex. *)
    left.
    (* Because `t1` is a closed value and has a function type,
       it must be a lambda-abstraction. *)
    forward invert_jf_TyFun. { eauto with closed. }
    (* Therefore, we have a beta-redex. *)
    obvious. }
  (* Case: JFTyAbs. *)
  { use_ih IHjf. eauto. }
  (* Case: JFTyApp. *)
  { use_ih IHjf. eauto. }
Qed.
